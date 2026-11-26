/* manybox: interval expressions written ONCE, compiled by nvcc (CUDA directed-rounding
   intrinsics) and by gcc (realfp's portable RN+error kernels, ../../../c/iv64_rnerr.h).
   Each expression is written in exactly the operation order of the Lean `IExpr` given in
   lean/ManyBox.lean, so the enclosures are bit-identical to realfp's kernel evaluator
   `evalK` (KI.add/sub/mul/pown/ofRat) and a GPU certificate is accepted by Lean as is.

   The includer defines IVQ (qualifiers) and ADD_D ADD_U SUB_D SUB_U MUL_D MUL_U.
   Endpoints are finite for these problems (no inf/NaN handling). */
#ifndef MBEXPR_H
#define MBEXPR_H
#define MB_MIN(a, b) ((a) < (b) ? (a) : (b))
#define MB_MAX(a, b) ((a) > (b) ? (a) : (b))

typedef struct { double lo, hi; } mbiv;

IVQ mbiv mb_c(double c) { mbiv r = {c, c}; return r; }
IVQ mbiv mb_add(mbiv a, mbiv b) { mbiv r = {ADD_D(a.lo, b.lo), ADD_U(a.hi, b.hi)}; return r; }
IVQ mbiv mb_sub(mbiv a, mbiv b) { mbiv r = {SUB_D(a.lo, b.hi), SUB_U(a.hi, b.lo)}; return r; }
/* KI.mul: [min of the 4 corners rounded down, max of the 4 corners rounded up]. */
IVQ mbiv mb_mul(mbiv x, mbiv y) {
  double a = x.lo, b = x.hi, c = y.lo, d = y.hi;
  double lo = MB_MIN(MB_MIN(MUL_D(a, c), MUL_D(a, d)), MB_MIN(MUL_D(b, c), MUL_D(b, d)));
  double hi = MB_MAX(MB_MAX(MUL_U(a, c), MUL_U(a, d)), MB_MAX(MUL_U(b, c), MUL_U(b, d)));
  mbiv r = {lo, hi}; return r;
}
/* KI.pown x 2 = [RD(m^2), RU(M^2)] with [m, M] = |x| (lo = 0 if x straddles 0). */
IVQ mbiv mb_sqr(mbiv x) {
  double m = x.lo >= 0 ? x.lo : (x.hi <= 0 ? -x.hi : 0.0);
  double M = MB_MAX(-x.lo, x.hi);
  mbiv r = {MUL_D(m, m), MUL_U(M, M)}; return r;
}
/* KI.pown x 4 = [RD(RD(m^2)^2), RU(RU(M^2)^2)] (repeated squaring of the endpoints). */
IVQ mbiv mb_pow4(mbiv x) {
  double m = x.lo >= 0 ? x.lo : (x.hi <= 0 ? -x.hi : 0.0);
  double M = MB_MAX(-x.lo, x.hi);
  double m2 = MUL_D(m, m), M2 = MUL_U(M, M);
  mbiv r = {MUL_D(m2, m2), MUL_U(M2, M2)}; return r;
}

/* P1: Chebyshev T8 from its monomial expansion, in Horner form in u = x^2:
     T8(x) = (((128 u - 256) u + 160) u - 32) u + 1,
   f(x, y) = T8(x) + T8(y).  Claim: f <= 2 + delta on [-1, 1]^2 (true max 2, attained at
   25 points (cos(2 i pi/8), cos(2 j pi/8))).  Lean:
     ((((128*x^2 - 256)*x^2 + 160)*x^2 - 32)*x^2 + 1) + (same in y) */
IVQ mbiv mb_t8(mbiv x) {
  mbiv u = mb_sqr(x);
  mbiv h = mb_sub(mb_mul(mb_c(128.0), u), mb_c(256.0));
  h = mb_add(mb_mul(h, u), mb_c(160.0));
  h = mb_sub(mb_mul(h, u), mb_c(32.0));
  return mb_add(mb_mul(h, u), mb_c(1.0));
}
IVQ mbiv mb_p1(const mbiv *X) { return mb_add(mb_t8(X[0]), mb_t8(X[1])); }

/* P2: Choi-Lam quartic (PSD, not a sum of squares)
     S(x, y, z, w) = x^2 y^2 + y^2 z^2 + z^2 x^2 + w^4 - 4 x y z w.
   Claim: S >= -delta on [-1, 1]^4 (true min 0, attained on the three coordinate axes in
   x, y, z and on the 8 lines t (+-1, +-1, +-1, 1) with an even number of minus signs).  Lean:
     x^2*y^2 + y^2*z^2 + z^2*x^2 + w^4 - 4*(x*y)*(z*w) */
IVQ mbiv mb_p2(const mbiv *X) {
  mbiv x2 = mb_sqr(X[0]), y2 = mb_sqr(X[1]), z2 = mb_sqr(X[2]);
  mbiv s = mb_add(mb_add(mb_add(mb_mul(x2, y2), mb_mul(y2, z2)), mb_mul(z2, x2)), mb_pow4(X[3]));
  mbiv t = mb_mul(mb_mul(mb_c(4.0), mb_mul(X[0], X[1])), mb_mul(X[2], X[3]));
  return mb_sub(s, t);
}
#endif
