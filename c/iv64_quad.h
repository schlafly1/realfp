/* Expression tapes and quadrature kernels for Interval64 (header-only).

   A tape is the reflected expression `IExpr` compiled (in Lean, `Interval64.Tape`) into
   straight-line code with common subexpressions shared: instruction `i` is three
   `uint32` words `op, a, b` and writes register `i`. Arithmetic is evaluated here with the
   same `Interval64` operations as `KF.evalI`; elementary functions (`exp`, `sin`, ...)
   call back into the Lean implementations (closures in `fns`), so they are the same
   functions. Quadrature routines transcribe `Quad.integrate` (cell0 / cell1),
   `integrate2E0/E1` and `KQ.quadF` (Taylor cells). */
#ifndef IV64_QUAD_H
#define IV64_QUAD_H

#include <lean/lean.h>
#include "iv64_poly.h"

enum { IVT_VAR = 0, IVT_CONST, IVT_ADD, IVT_SUB, IVT_MUL, IVT_DIV, IVT_NEG, IVT_INV, IVT_SQRT,
       IVT_ABS, IVT_POW, IVT_FN, IVT_ATAN2 };

typedef struct {
  const uint32_t *code; size_t len;   /* len instructions (3 words each) */
  const double *k;                    /* constants: lo, hi pairs */
  b_lean_obj_arg fns;                 /* Array (Interval64 → Interval64) */
  b_lean_obj_arg atan2fn;             /* Interval64 → Interval64 → Interval64 */
  ivp_t *regs;
} ivt_t;

static inline lean_object *ivt_box(ivp_t x) {
  lean_object *o = lean_alloc_ctor(0, 0, 16);
  lean_ctor_set_float(o, 0, x.lo);
  lean_ctor_set_float(o, 8, x.hi);
  return o;
}
static inline ivp_t ivt_unbox(b_lean_obj_arg o) {
  return (ivp_t){ lean_ctor_get_float(o, 0), lean_ctor_get_float(o, 8) };
}

/* Evaluate instructions 0..upto (inclusive) on env; returns register upto. */
static ivp_t ivt_eval(ivt_t *t, const ivp_t *env, size_t nenv, size_t upto) {
  ivp_t *R = t->regs;
  for (size_t i = 0; i <= upto; i++) {
    uint32_t op = t->code[3 * i], a = t->code[3 * i + 1], b = t->code[3 * i + 2];
    ivp_t r;
    switch (op) {
      case IVT_VAR: r = a < nenv ? env[a] : ivp_zero(); break;
      case IVT_CONST: r = (ivp_t){ t->k[2 * a], t->k[2 * a + 1] }; break;
      case IVT_ADD: r = ivp_add(R[a], R[b]); break;
      case IVT_SUB: r = ivp_sub(R[a], R[b]); break;
      case IVT_MUL: r = ivp_mul(R[a], R[b]); break;
      case IVT_DIV: r = ivp_mul(R[a], ivp_inv(R[b])); break;
      case IVT_NEG: r = ivp_neg(R[a]); break;
      case IVT_INV: r = ivp_inv(R[a]); break;
      case IVT_SQRT: r = ivp_sqrtI(R[a]); break;
      case IVT_ABS: r = ivp_abs(R[a]); break;
      case IVT_POW: r = ivp_pown(R[a], b); break;
      case IVT_FN: {
        lean_object *f = lean_array_get_core(t->fns, b);
        lean_inc(f);
        lean_object *res = lean_apply_1(f, ivt_box(R[a]));
        r = ivt_unbox(res);
        lean_dec(res);
        break;
      }
      default: { /* IVT_ATAN2 */
        lean_inc(t->atan2fn);
        lean_object *res = lean_apply_2(t->atan2fn, ivt_box(R[a]), ivt_box(R[b]));
        r = ivt_unbox(res);
        lean_dec(res);
        break;
      }
    }
    R[i] = r;
  }
  return R[upto];
}

/* ---------- adaptive 1D / iterated 2D quadrature (Quad.integrate) ---------- */

typedef struct ivq_ctx {
  ivt_t *t;
  int order;              /* 0: cell0, 1: cell1 */
  size_t v;               /* integration variable */
  ivp_t env[2]; size_t nenv;
  size_t rF, rD;          /* registers of e and its derivative (order 1) */
  struct ivq_ctx *inner;  /* 2D: the integrand on an x-cell is the inner integral */
  double c, d, tol; size_t fuel;   /* inner integral parameters */
} ivq_ctx;

static ivp_t ivq_integrate(ivq_ctx *q, double a, double b, double tol, size_t fuel);

static inline ivp_t ivq_F(ivq_ctx *q, ivp_t X) {
  if (q->inner) {
    q->inner->env[0] = X;
    return ivq_integrate(q->inner, q->inner->c, q->inner->d, q->inner->tol, q->inner->fuel);
  }
  q->env[q->v] = X;
  return ivt_eval(q->t, q->env, q->nenv, q->rF);
}

static inline ivp_t ivq_cell0(ivq_ctx *q, double lo, double hi) {
  return ivp_mul(ivq_F(q, (ivp_t){ lo, hi }), ivp_sub(ivp_point(hi), ivp_point(lo)));
}

static inline ivp_t ivq_cell1(ivq_ctx *q, double lo, double hi) {
  ivp_t X = { lo, hi };
  double m = ivp_mid(X);
  if (isinf(m)) return ivq_cell0(q, lo, hi);
  ivp_t M = ivp_point(m);
  q->env[q->v] = X;
  size_t top = q->rF > q->rD ? q->rF : q->rD;
  ivt_eval(q->t, q->env, q->nenv, top);
  ivp_t FX = q->t->regs[q->rF], DX = q->t->regs[q->rD];
  ivp_t W = ivp_sub(ivp_point(hi), ivp_point(lo));
  ivp_t c0 = ivp_mul(FX, W);
  ivp_t half = { 0.5, 0.5 };
  ivp_t Qa = ivp_mul(ivp_square(ivp_sub(ivp_point(hi), M)), half);
  ivp_t Qb = ivp_mul(ivp_square(ivp_sub(M, ivp_point(lo))), half);
  q->env[q->v] = M;
  ivp_t FM = ivt_eval(q->t, q->env, q->nenv, q->rF);
  return ivp_intersect(c0, ivp_add(ivp_add(ivp_mul(FM, W), ivp_mul(DX, Qa)), ivp_mul(ivp_neg(DX), Qb)));
}

static inline ivp_t ivq_cell(ivq_ctx *q, double lo, double hi) {
  return q->order ? ivq_cell1(q, lo, hi) : ivq_cell0(q, lo, hi);
}

/* Quad.quadAux */
static ivp_t ivq_aux(ivq_ctx *q, size_t fuel, double tol, double lo, double hi) {
  ivp_t R = ivq_cell(q, lo, hi);
  if (fuel == 0) return R;
  if (ivp_width(R) <= tol) return R;
  double m = ivp_mid((ivp_t){ lo, hi });
  ivp_t A = ivq_aux(q, fuel - 1, tol / 2, lo, m);
  ivp_t B = ivq_aux(q, fuel - 1, tol / 2, m, hi);
  return ivp_add(A, B);
}

/* Quad.integrate */
static ivp_t ivq_integrate(ivq_ctx *q, double a, double b, double tol, size_t fuel) {
  if (ivp_finite(a) && ivp_finite(b) && a <= b) return ivq_aux(q, fuel, tol, a, b);
  return ivp_whole();
}

/* ---------- Taylor cells (KQ.quadF) ---------- */

/* ofRat (1 / (j+1)!) for (j+1)! < 2^53, i.e. j + 1 <= 18. */
static inline ivp_t ivq_invfact(size_t n) {
  double f = 1.0;
  for (size_t i = 2; i <= n; i++) f *= (double)i;
  return (ivp_t){ div_dn(1.0, f), div_up(1.0, f) };
}

/* KQ.momF lo m hi j */
static inline ivp_t ivq_mom(double lo, double m, double hi, size_t j) {
  ivp_t a = ivp_pown(ivp_sub(ivp_point(hi), ivp_point(m)), j + 1);
  ivp_t b = ivp_pown(ivp_sub(ivp_point(lo), ivp_point(m)), j + 1);
  return ivp_mul(ivp_sub(a, b), ivq_invfact(j + 1));
}

/* KQ.cellF: roots[0..K] are the registers of d_0 .. d_K. tmp has K entries. */
static inline ivp_t ivq_taylor_cell(ivt_t *t, const size_t *roots, size_t K, double lo, double m, double hi,
                                    ivp_t *tmp) {
  size_t top = 0;
  for (size_t j = 0; j < K; j++) if (roots[j] > top) top = roots[j];
  ivp_t pm = ivp_point(m);
  ivt_eval(t, &pm, 1, top);
  for (size_t j = 0; j < K; j++) tmp[j] = t->regs[roots[j]];
  ivp_t acc = ivp_zero();
  for (size_t j = K; j-- > 0;) acc = ivp_add(ivp_mul(tmp[j], ivq_mom(lo, m, hi, j)), acc);
  ivp_t X = { lo, hi };
  ivp_t dK = ivt_eval(t, &X, 1, roots[K]);
  ivp_t rem = ivp_mul(dK, ivq_mom(lo, m, hi, K));
  return ivp_add(acc, rem);
}

#endif
