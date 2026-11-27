/* manybox C batch checker: the runtime of `ManyBox.checkHex` (lean/fast/ManyBoxTape.lean).

   TRUSTED (under native_decide): this file must compute exactly the Lean specification
     checkC3 fe (if upper then gLe c else gGe c) (decodeCertC d hex) env
   (or, for `checkHexAt`, the same on `decC d hex l0 cs0`: a subtree rooted at depth l0 with
   integer coordinates cs0) whenever `checkHexImpl` / `checkHexAtImpl` calls it (a straight-line
   tape for `fe` with ops var/const/add/sub/mul/neg/pow/div/sqrt only; d = length of env,
   1 <= d <= 16; c < 2^64). Every Lean definition it mirrors
   is named in the comments. Directed rounding uses realfp's own runtime kernels
   `iv64_dir_*` (AVX-512 or RN+error backend, exactly what `addDown` etc. run natively), so the
   only new trusted code is the control flow below. Any doubt (out-of-range coordinate or
   shift, unknown opcode, tape too long) returns 0 (= false), which can only make a check fail.

   Tape (`ManyBox.toTape`): instruction k = three little-endian u32 (op, a, b), result in
   register k; op 0 var a | 1 const a (consts[2a], consts[2a+1]) | 2 add a b | 3 sub a b |
   4 mul a b | 5 neg a | 6 pow a b (exponent b) | 7 div a b (= a * inv b, as evalFE) |
   8 sqrt a (sqrtI). The last register is the expression value. */
#include <lean/lean.h>
#include <math.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <pthread.h>
#include <stddef.h>
#include <unistd.h>

double iv64_dir_add_down(double a, double b);
double iv64_dir_add_up(double a, double b);
double iv64_dir_sub_down(double a, double b);
double iv64_dir_sub_up(double a, double b);
double iv64_dir_mul_down(double a, double b);
double iv64_dir_mul_up(double a, double b);
double iv64_dir_div_down(double a, double b);
double iv64_dir_div_up(double a, double b);
double iv64_dir_sqrt_down(double a);
double iv64_dir_sqrt_up(double a);

#define MB_MAXREG 4096
#define MB_MAXD 16

typedef struct { double lo, hi; } iv;

static const iv IV_INVALID = {NAN, NAN};          /* Interval64.invalid */

static inline int anynan(iv a, iv b) { return isnan(a.lo) || isnan(a.hi) || isnan(b.lo) || isnan(b.hi); }

/* Interval64.add / sub */
static inline iv iv_add(iv a, iv b) {
  if (anynan(a, b)) return IV_INVALID;
  iv r = {iv64_dir_add_down(a.lo, b.lo), iv64_dir_add_up(a.hi, b.hi)}; return r;
}
static inline iv iv_sub(iv a, iv b) {
  if (anynan(a, b)) return IV_INVALID;
  iv r = {iv64_dir_sub_down(a.lo, b.hi), iv64_dir_sub_up(a.hi, b.lo)}; return r;
}
/* Interval64.accCorner */
static inline void acc_corner(double x, double y, double *lo, double *hi, int *got) {
  if ((x == 0 && isinf(y)) || (y == 0 && isinf(x))) return;
  double d = iv64_dir_mul_down(x, y), u = iv64_dir_mul_up(x, y);
  if (isnan(d) || isnan(u)) return;
  if (!*got) { *lo = d; *hi = u; *got = 1; return; }
  *lo = (d < *lo) ? d : *lo;            /* if decide (d < lo) then d else lo */
  *hi = (u > *hi) ? u : *hi;            /* if decide (u > hi) then u else hi */
}
/* Interval64.mul */
static inline iv iv_mul(iv a, iv b) {
  if (anynan(a, b)) return IV_INVALID;
  double lo = 0, hi = 0; int got = 0;
  acc_corner(a.lo, b.lo, &lo, &hi, &got);
  acc_corner(a.lo, b.hi, &lo, &hi, &got);
  acc_corner(a.hi, b.lo, &lo, &hi, &got);
  acc_corner(a.hi, b.hi, &lo, &hi, &got);
  if (!got) { iv w = {-INFINITY, INFINITY}; return w; }   /* Interval64.whole */
  iv r = {lo, hi}; return r;
}
/* Interval64.neg (no NaN test) */
static inline iv iv_neg(iv a) { iv r = {-a.hi, -a.lo}; return r; }
/* fmax x y := if decide (x > y) then x else y */
static inline double fmax_l(double x, double y) { return (x > y) ? x : y; }
/* Interval64.abs */
static inline iv iv_abs(iv a) {
  if (isnan(a.lo) || isnan(a.hi)) return IV_INVALID;
  if (0 <= a.lo) return a;
  if (a.hi <= 0) { iv r = {-a.hi, -a.lo}; return r; }
  iv r = {0.0, fmax_l(-a.lo, a.hi)}; return r;
}
/* Interval64.square */
static inline iv iv_square(iv a) {
  if (isnan(a.lo) || isnan(a.hi)) return IV_INVALID;
  if (0 <= a.lo) { iv r = {iv64_dir_mul_down(a.lo, a.lo), iv64_dir_mul_up(a.hi, a.hi)}; return r; }
  if (a.hi <= 0) { iv r = {iv64_dir_mul_down(a.hi, a.hi), iv64_dir_mul_up(a.lo, a.lo)}; return r; }
  iv r = {0.0, fmax_l(iv64_dir_mul_up(a.lo, a.lo), iv64_dir_mul_up(a.hi, a.hi))}; return r;
}
/* Interval64.ipow b e = ipowAux 64 b e [1,1]; e < 2^32 here, so the fuel never runs out */
static inline iv iv_ipow(iv b, uint32_t e) {
  iv acc = {1.0, 1.0};
  for (int fuel = 64; fuel > 0; fuel--) {
    if (e == 0) return acc;
    iv nb = iv_square(b);
    if (e % 2 == 1) acc = iv_mul(acc, b);
    b = nb; e /= 2;
  }
  if (e == 0) return acc;
  iv w = {-INFINITY, INFINITY}; return w;
}
/* Interval64.powLo / powHi */
static inline double pow_lo(double f, uint32_t n) { if (isinf(f)) return f; iv p = {f, f}; return iv_ipow(p, n).lo; }
static inline double pow_hi(double f, uint32_t n) { if (isinf(f)) return f; iv p = {f, f}; return iv_ipow(p, n).hi; }
/* Interval64.pown */
static inline iv iv_pown(iv a, uint32_t n) {
  if (isnan(a.lo) || isnan(a.hi)) return IV_INVALID;
  if (n == 0) { iv r = {1.0, 1.0}; return r; }
  if (n % 2 == 1) { iv r = {pow_lo(a.lo, n), pow_hi(a.hi, n)}; return r; }
  iv b = iv_abs(a);
  iv r = {pow_lo(b.lo, n), pow_hi(b.hi, n)}; return r;
}

/* Interval64.containsZero: !isInvalid i && decide (i.lo <= 0) && decide (0 <= i.hi) */
static inline int contains_zero(iv a) { return !(isnan(a.lo) || isnan(a.hi)) && a.lo <= 0 && 0 <= a.hi; }
/* Interval64.inv */
static inline iv iv_inv(iv a) {
  if (isnan(a.lo) || isnan(a.hi)) return IV_INVALID;
  if (contains_zero(a)) { iv w = {-INFINITY, INFINITY}; return w; }   /* whole */
  iv r = {iv64_dir_div_down(1.0, a.hi), iv64_dir_div_up(1.0, a.lo)}; return r;
}
/* fmin x y := if decide (x < y) then x else y */
static inline double fmin_l(double x, double y) { return (x < y) ? x : y; }
/* Interval64.sqrt (Interval.lean) */
static inline iv iv_sqrt(iv a) {
  if (isnan(a.lo) || isnan(a.hi)) return IV_INVALID;
  if (a.hi < 0) return IV_INVALID;
  double l = (a.lo < 0) ? 0.0 : a.lo;
  iv r = {iv64_dir_sqrt_down(l), iv64_dir_sqrt_up(a.hi)}; return r;
}
/* Interval64.hull */
static inline iv iv_hull(iv a, iv b) {
  if (isnan(a.lo) || isnan(a.hi)) return b;
  if (isnan(b.lo) || isnan(b.hi)) return a;
  iv r = {fmin_l(a.lo, b.lo), fmax_l(a.hi, b.hi)}; return r;
}
/* KF.sqrtI X := if decide (X.lo < 0) then hull zeroI (Interval64.sqrt X) else Interval64.sqrt X */
static inline iv iv_sqrtI(iv a) {
  if (a.lo < 0) { iv z = {0.0, 0.0}; return iv_hull(z, iv_sqrt(a)); }
  return iv_sqrt(a);
}

/* Interval64.KF.cmp / le on bit patterns (0 lt, 1 eq, 2 gt, 3 unordered) */
static inline uint64_t magB(uint64_t n) { return n & 0x7FFFFFFFFFFFFFFFull; }
static inline int kf_isnan(uint64_t n) { return magB(n) > 0x7FF0000000000000ull; }
static inline int kf_isinf(uint64_t n) { return magB(n) == 0x7FF0000000000000ull; }
static inline int kf_iszero(uint64_t n) { return magB(n) == 0; }
static inline uint64_t kf_sgn(uint64_t n) { return n >> 63; }
static inline uint64_t kf_ex(uint64_t n) { return magB(n) >> 52; }
static inline uint64_t kf_fr(uint64_t n) { return n & 0xFFFFFFFFFFFFFull; }
static inline uint64_t kf_mant(uint64_t n) { return kf_ex(n) == 0 ? kf_fr(n) : kf_fr(n) + 0x10000000000000ull; }
static inline uint64_t kf_qexp(uint64_t n) { return kf_ex(n) == 0 ? 1 : kf_ex(n); }
static inline int kf_cmpmag(uint64_t a, uint64_t b) {
  if (kf_qexp(a) < kf_qexp(b)) return 0;
  if (kf_qexp(b) < kf_qexp(a)) return 2;
  if (kf_mant(a) < kf_mant(b)) return 0;
  if (kf_mant(b) < kf_mant(a)) return 2;
  return 1;
}
static int kf_cmp(uint64_t a, uint64_t b) {
  if (kf_isnan(a) || kf_isnan(b)) return 3;
  if (kf_isinf(a)) {
    if (kf_isinf(b)) return kf_sgn(a) == kf_sgn(b) ? 1 : (kf_sgn(a) == 1 ? 0 : 2);
    return kf_sgn(a) == 0 ? 2 : 0;
  }
  if (kf_isinf(b)) return kf_sgn(b) == 0 ? 0 : 2;
  if (kf_iszero(a)) return kf_iszero(b) ? 1 : (kf_sgn(b) == 0 ? 0 : 2);
  if (kf_iszero(b)) return kf_sgn(a) == 0 ? 2 : 0;
  if (kf_sgn(a) == 1) return kf_sgn(b) == 1 ? 2 - kf_cmpmag(a, b) : 0;
  if (kf_sgn(b) == 1) return 2;
  return kf_cmpmag(a, b);
}
static inline int kf_le(uint64_t a, uint64_t b) { return kf_cmp(a, b) < 2; }
static inline uint64_t bits(double x) { uint64_t u; memcpy(&u, &x, 8); return u; }

typedef struct {
  const uint32_t *code; uint32_t n;         /* tape */
  const double *k; size_t nk;               /* constants (lo, hi pairs) */
  int upper; uint64_t c;                    /* goal: gLe c (upper) or gGe c */
  uint32_t d;
  const uint8_t *s; size_t slen;            /* hex string */
  size_t pos;                               /* next bit */
  iv env[MB_MAXD];
  uint64_t cs[MB_MAXD];                     /* integer box coordinates (decC) */
  iv reg[MB_MAXREG];
} st_t;

/* evalFE env fe on the tape; then g (bitsOf r) */
static int leaf_ok(st_t *S) {
  iv *R = S->reg;
  for (uint32_t k = 0; k < S->n; k++) {
    uint32_t op = S->code[3 * k], a = S->code[3 * k + 1], b = S->code[3 * k + 2];
    switch (op) {
      case 0: { iv z = {0.0, 0.0}; R[k] = a < S->d ? S->env[a] : z; break; }  /* env.getD a zeroI */
      case 1: R[k].lo = S->k[2 * a]; R[k].hi = S->k[2 * a + 1]; break;
      case 2: R[k] = iv_add(R[a], R[b]); break;
      case 3: R[k] = iv_sub(R[a], R[b]); break;
      case 4: R[k] = iv_mul(R[a], R[b]); break;
      case 5: R[k] = iv_neg(R[a]); break;
      case 6: R[k] = iv_pown(R[a], b); break;
      case 7: R[k] = iv_mul(R[a], iv_inv(R[b])); break;     /* evalFE (.div a b) = a * inv b */
      case 8: R[k] = iv_sqrtI(R[a]); break;
      default: return 0;
    }
  }
  iv F = R[S->n - 1];
  uint64_t lo = bits(F.lo), hi = bits(F.hi);
  if (kf_isnan(lo) || kf_isnan(hi) || kf_isnan(S->c)) return 0;
  return S->upper ? kf_le(hi, S->c) : kf_le(S->c, lo);    /* gLe c F / gGe c F */
}

/* bitAtC */
static inline int bit_at(const st_t *S, size_t i) {
  size_t j = i / 4;
  if (j >= S->slen) return 0;                              /* get! default */
  uint8_t ch = S->s[j]; unsigned v;
  if (ch >= 48 && ch <= 57) v = ch - 48; else if (ch >= 97 && ch <= 102) v = ch - 87; else v = 0;
  return (v >> (3 - i % 4)) & 1;
}

/* decC and checkC3 fused: returns checkC3 on the subtree starting at bit S->pos, and
   advances S->pos exactly as decC does whenever the result is 1. */
static int walk(st_t *S, uint32_t l) {
  if (!bit_at(S, S->pos)) { S->pos++; return leaf_ok(S); }
  S->pos++;
  uint32_t d = S->d, i = l % d;
  uint32_t sp = (l + d - 1 - i) / d;
  uint64_t c = S->cs[i];
  /* midBitsC c sp = (-1 + (2c+1).toFloat * scaleB 1 (-sp)).toBits: exact here */
  if (c >= (1ull << 51) || sp > 1000) return 0;
  double m = -1.0 + (double)(2 * c + 1) * ldexp(1.0, -(int)sp);
  if (isnan(m)) return 0;                                  /* !isNaN m (m < 2^64 always) */
  iv save = S->env[i];
  S->env[i].hi = m; S->cs[i] = 2 * c;
  int ok = walk(S, l + 1);
  if (ok) {
    S->env[i].lo = m; S->env[i].hi = save.hi; S->cs[i] = 2 * c + 1;
    ok = walk(S, l + 1);
  }
  S->env[i] = save; S->cs[i] = c;
  return ok;
}

/* Skip the subtree starting at bit `pos` (the bit-only part of decC): returns the bit after it. */
static size_t skip_tree(const st_t *S, size_t pos) {
  size_t pending = 1;                       /* subtrees still to read */
  while (pending) { pending--; if (bit_at(S, pos++)) pending += 2; }
  return pos;
}

/* Parallel walk. The spec's value is the conjunction, over the decoded tree, of the midpoint
   tests at the splits and the goal at the leaves (`&&` is commutative on these pure values; the
   short-circuit only skips work). The top of the tree is walked serially down to depth `cut`;
   each subtree found there becomes a task, evaluated by `walk` on a private copy of the state. */
typedef struct { size_t pos; uint32_t l; iv env[MB_MAXD]; uint64_t cs[MB_MAXD]; } task_t;
typedef struct { task_t *t; size_t n, cap; } tasks_t;

static int top(st_t *S, uint32_t l, uint32_t cut, tasks_t *T) {
  if (l == cut) {
    if (T->n == T->cap) {
      size_t nc = T->cap ? 2 * T->cap : 1024;
      task_t *p = (task_t *)realloc(T->t, nc * sizeof(task_t));
      if (!p) return 0;
      T->t = p; T->cap = nc;
    }
    task_t *t = &T->t[T->n++];
    t->pos = S->pos; t->l = l;
    memcpy(t->env, S->env, sizeof S->env); memcpy(t->cs, S->cs, sizeof S->cs);
    S->pos = skip_tree(S, S->pos);
    return 1;
  }
  if (!bit_at(S, S->pos)) { S->pos++; return leaf_ok(S); }
  S->pos++;
  uint32_t d = S->d, i = l % d;
  uint32_t sp = (l + d - 1 - i) / d;
  uint64_t c = S->cs[i];
  if (c >= (1ull << 51) || sp > 1000) return 0;
  double m = -1.0 + (double)(2 * c + 1) * ldexp(1.0, -(int)sp);
  if (isnan(m)) return 0;
  iv save = S->env[i];
  S->env[i].hi = m; S->cs[i] = 2 * c;
  int ok = top(S, l + 1, cut, T);
  if (ok) {
    S->env[i].lo = m; S->env[i].hi = save.hi; S->cs[i] = 2 * c + 1;
    ok = top(S, l + 1, cut, T);
  }
  S->env[i] = save; S->cs[i] = c;
  return ok;
}

typedef struct {
  const st_t *proto; tasks_t *T;
  size_t *next; int *fail;
} worker_t;

static void *worker(void *arg) {
  worker_t *W = (worker_t *)arg;
  st_t *S = (st_t *)malloc(sizeof(st_t));
  if (!S) { __atomic_store_n(W->fail, 1, __ATOMIC_RELEASE); return NULL; }
  memcpy(S, W->proto, offsetof(st_t, reg));                /* everything but the registers */
  for (;;) {
    if (__atomic_load_n(W->fail, __ATOMIC_ACQUIRE)) break;
    size_t k = __atomic_fetch_add(W->next, 1, __ATOMIC_ACQ_REL);
    if (k >= W->T->n) break;
    const task_t *t = &W->T->t[k];
    S->pos = t->pos;
    memcpy(S->env, t->env, sizeof S->env); memcpy(S->cs, t->cs, sizeof S->cs);
    if (!walk(S, t->l)) { __atomic_store_n(W->fail, 1, __ATOMIC_RELEASE); break; }
  }
  free(S);
  return NULL;
}

/* Number of threads: MB_THREADS if set (1 = serial), else the online CPUs (at most 64). */
static int n_threads(void) {
  const char *e = getenv("MB_THREADS");
  long n = e ? atol(e) : sysconf(_SC_NPROCESSORS_ONLN);
  if (n < 1) n = 1;
  if (n > 64) n = 64;
  return (int)n;
}

/* Common entry: tree rooted at depth l0 with integer coordinates cs0 (decC d s l0 cs0 0). */
static uint8_t check_at(b_lean_obj_arg code, b_lean_obj_arg consts, uint8_t upper, uint64_t c,
                        uint32_t d, uint32_t l0, const uint64_t *cs0, b_lean_obj_arg hex,
                        b_lean_obj_arg box) {
  static __thread st_t S;   /* large (register file); one check at a time per thread */
  const uint32_t one = 1;
  if (*(const uint8_t *)&one != 1) return 0;               /* tape is little-endian */
  size_t nb = lean_sarray_size(code);
  if (nb % 12 != 0 || nb == 0 || nb / 12 > MB_MAXREG) return 0;
  if (d == 0 || d > MB_MAXD || lean_sarray_size(box) != 2 * (size_t)d) return 0;
  S.n = (uint32_t)(nb / 12);
  S.code = (const uint32_t *)lean_sarray_cptr(code);       /* little-endian hosts only */
  S.nk = lean_sarray_size(consts) / 2;
  S.k = lean_float_array_cptr(consts);
  /* validate the tape once: operands refer to earlier registers / existing constants */
  for (uint32_t k = 0; k < S.n; k++) {
    uint32_t op = S.code[3 * k], a = S.code[3 * k + 1], b = S.code[3 * k + 2];
    if (op > 8) return 0;
    if (op == 1 && a >= S.nk) return 0;
    if ((op >= 2 && op <= 8) && a >= k) return 0;
    if (((op >= 2 && op <= 4) || op == 7) && b >= k) return 0;
  }
  S.upper = upper != 0; S.c = c; S.d = d;
  S.s = (const uint8_t *)lean_string_cstr(hex);
  S.slen = lean_string_size(hex) - 1;                      /* UTF-8 bytes without the NUL */
  const double *bx = lean_float_array_cptr(box);
  for (uint32_t j = 0; j < d; j++) {
    S.env[j].lo = bx[2 * j]; S.env[j].hi = bx[2 * j + 1]; S.cs[j] = cs0 ? cs0[j] : 0;
  }
  S.pos = 0;
  if (l0 > (1u << 20)) return 0;
  int nt = n_threads();
  if (nt == 1) return (uint8_t)walk(&S, l0);
  /* cut depth (affects speed only): at least 64 subtrees per thread, and about 2^(L-6)
     subtrees for a certificate of 2^L bits (bisection trees are very unbalanced) */
  uint32_t cut = 0; while ((1u << cut) < 64u * (unsigned)nt && cut < 24) cut++;
  uint32_t L = 0; while (L < 62 && (4 * (uint64_t)S.slen >> (L + 1)) != 0) L++;
  if (L >= 6 && L - 6 > cut) cut = L - 6;
  if (cut > 24) cut = 24;
  const char *ce = getenv("MB_CUT");                       /* tuning only */
  if (ce) { long v = atol(ce); if (v >= 0 && v <= 40) cut = (uint32_t)v; }
  tasks_t T = {NULL, 0, 0};
  int ok = top(&S, l0, l0 + cut, &T);
  if (ok && T.n > 0) {
    size_t next = 0; int fail = 0;
    pthread_t th[64]; worker_t W[64]; int started = 0;
    for (int j = 0; j < nt; j++) {
      W[j].proto = &S; W[j].T = &T; W[j].next = &next; W[j].fail = &fail;
      if (pthread_create(&th[j], NULL, worker, &W[j]) != 0) { fail = 1; break; }
      started++;
    }
    for (int j = 0; j < started; j++) pthread_join(th[j], NULL);
    /* a task not run (failed thread start, early stop) leaves fail = 1 or next < n */
    ok = !fail && next >= T.n;   /* every task was taken and none failed */
  }
  free(T.t);
  return (uint8_t)ok;
}

/* @[extern "mb_check_tape"] opaque checkTapeExt (code : @& ByteArray) (consts : @& FloatArray)
     (upper : UInt8) (c : UInt64) (d : UInt32) (hex : @& String) (box : @& FloatArray) : Bool */
LEAN_EXPORT uint8_t mb_check_tape(b_lean_obj_arg code, b_lean_obj_arg consts, uint8_t upper,
                                  uint64_t c, uint32_t d, b_lean_obj_arg hex, b_lean_obj_arg box) {
  return check_at(code, consts, upper, c, d, 0, NULL, hex, box);
}

/* @[extern "mb_check_tape_at"] opaque checkTapeAtExt (code : @& ByteArray) (consts : @& FloatArray)
     (upper : UInt8) (c : UInt64) (d : UInt32) (l0 : UInt32) (cs0 : @& ByteArray) (hex : @& String)
     (box : @& FloatArray) : Bool    -- cs0: d little-endian u64 */
LEAN_EXPORT uint8_t mb_check_tape_at(b_lean_obj_arg code, b_lean_obj_arg consts, uint8_t upper,
                                     uint64_t c, uint32_t d, uint32_t l0, b_lean_obj_arg cs0,
                                     b_lean_obj_arg hex, b_lean_obj_arg box) {
  if (d == 0 || d > MB_MAXD || lean_sarray_size(cs0) != 8 * (size_t)d) return 0;
  uint64_t cs[MB_MAXD];
  const uint8_t *p = lean_sarray_cptr(cs0);
  for (uint32_t j = 0; j < d; j++) {
    uint64_t v = 0;
    for (int b = 7; b >= 0; b--) v = (v << 8) | p[8 * j + b];
    cs[j] = v;
  }
  return check_at(code, consts, upper, c, d, l0, cs, hex, box);
}
