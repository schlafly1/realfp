/* Interval64 GPU benchmark: the interval expressions, written ONCE and compiled
   both by nvcc (CUDA directed-rounding intrinsics) and by gcc (the repo's
   round-to-nearest + exact-error kernels, or fesetround), so every backend runs
   literally the same algorithm.

   The includer defines:
     IVQ                   function qualifiers ("static inline", "__device__ ...")
     IVT                   the float type (double or float)
     IVN(name)             name mangling for this instantiation
     ADD_D ADD_U SUB_D SUB_U MUL_D MUL_U DIV_D DIV_U SQRT_D SQRT_U
                           directed-rounding scalar ops (_D toward -inf, _U toward +inf)
   Everything is branch-free (only ?: selects, which compile to select/min/max).
   Endpoints are assumed finite (true for the benchmark boxes). */

#define IV_MIN(a, b) ((a) < (b) ? (a) : (b))
#define IV_MAX(a, b) ((a) > (b) ? (a) : (b))

typedef struct { IVT lo, hi; } IVN(iv);

IVQ IVN(iv) IVN(iv_c)(IVT c) { IVN(iv) r = {c, c}; return r; }

IVQ IVN(iv) IVN(iv_add)(IVN(iv) a, IVN(iv) b) {
  IVN(iv) r = {ADD_D(a.lo, b.lo), ADD_U(a.hi, b.hi)}; return r;
}
IVQ IVN(iv) IVN(iv_sub)(IVN(iv) a, IVN(iv) b) {
  IVN(iv) r = {SUB_D(a.lo, b.hi), SUB_U(a.hi, b.lo)}; return r;
}
/* General product: min / max of the 4 corner products, each rounded outward. */
IVQ IVN(iv) IVN(iv_mul)(IVN(iv) x, IVN(iv) y) {
  IVT a = x.lo, b = x.hi, c = y.lo, d = y.hi;
  IVT lo = IV_MIN(IV_MIN(MUL_D(a, c), MUL_D(a, d)), IV_MIN(MUL_D(b, c), MUL_D(b, d)));
  IVT hi = IV_MAX(IV_MAX(MUL_U(a, c), MUL_U(a, d)), IV_MAX(MUL_U(b, c), MUL_U(b, d)));
  IVN(iv) r = {lo, hi}; return r;
}
/* Square, knowing x^2 >= 0. */
IVQ IVN(iv) IVN(iv_sqr)(IVN(iv) x) {
  IVT ld = MUL_D(x.lo, x.lo), hd = MUL_D(x.hi, x.hi);
  IVT lu = MUL_U(x.lo, x.lo), hu = MUL_U(x.hi, x.hi);
  IVT lo = x.lo > 0 ? ld : (x.hi < 0 ? hd : (IVT)0);
  IVN(iv) r = {lo, IV_MAX(lu, hu)}; return r;
}
/* Quotient by an interval not containing 0 (else the whole line). */
IVQ IVN(iv) IVN(iv_div)(IVN(iv) x, IVN(iv) y) {
  IVT a = x.lo, b = x.hi, c = y.lo, d = y.hi;
  IVT lo = IV_MIN(IV_MIN(DIV_D(a, c), DIV_D(a, d)), IV_MIN(DIV_D(b, c), DIV_D(b, d)));
  IVT hi = IV_MAX(IV_MAX(DIV_U(a, c), DIV_U(a, d)), IV_MAX(DIV_U(b, c), DIV_U(b, d)));
  int ok = (c > 0) | (d < 0);
  IVN(iv) r = {ok ? lo : (IVT)(-INFINITY), ok ? hi : (IVT)INFINITY}; return r;
}
IVQ IVN(iv) IVN(iv_sqrt)(IVN(iv) x) {   /* x.hi >= 0 assumed */
  IVN(iv) r = {SQRT_D(IV_MAX(x.lo, (IVT)0)), SQRT_U(x.hi)}; return r;
}

/* f0: Motzkin polynomial  x^4 y^2 + x^2 y^4 - 3 x^2 y^2 + 1  (>= 0, = 0 at |x|=|y|=1),
       evaluated as  x^2 y^2 (x^2 + y^2 - 3) + 1.          Claim: f0 >= -1/64 on [-2,2]^2.
   f1: (x + y) / sqrt(2 (x^2 + y^2 + 1))  (< 1 everywhere).
                                                        Claim: f1 <= 0.99 on [-4,4]^2
       (true max on that square is 8/sqrt(66) = 0.98473...). */
IVQ IVN(iv) IVN(iv_f0)(IVN(iv) X, IVN(iv) Y) {
  IVN(iv) X2 = IVN(iv_sqr)(X), Y2 = IVN(iv_sqr)(Y);
  IVN(iv) P = IVN(iv_mul)(X2, Y2);
  IVN(iv) S = IVN(iv_sub)(IVN(iv_add)(X2, Y2), IVN(iv_c)((IVT)3));
  return IVN(iv_add)(IVN(iv_mul)(P, S), IVN(iv_c)((IVT)1));
}
IVQ IVN(iv) IVN(iv_f1)(IVN(iv) X, IVN(iv) Y) {
  IVN(iv) X2 = IVN(iv_sqr)(X), Y2 = IVN(iv_sqr)(Y);
  IVN(iv) D = IVN(iv_add)(IVN(iv_add)(X2, Y2), IVN(iv_c)((IVT)1));
  IVN(iv) R = IVN(iv_sqrt)(IVN(iv_mul)(IVN(iv_c)((IVT)2), D));
  return IVN(iv_div)(IVN(iv_add)(X, Y), R);
}
IVQ IVN(iv) IVN(iv_eval)(int fn, IVN(iv) X, IVN(iv) Y) {
  return fn == 0 ? IVN(iv_f0)(X, Y) : IVN(iv_f1)(X, Y);
}
