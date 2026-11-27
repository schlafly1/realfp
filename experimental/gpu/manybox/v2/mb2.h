/* manybox v2: problems and interval operations, written once as C++ templates and compiled by
   nvcc (CUDA directed-rounding intrinsics, fp64 or fp32) and by g++ (realfp's portable RN+error
   kernels, fp64). Every problem is written in exactly the operation order of its Lean `IExpr`
   (../lean/ManyBoxCert.lean, ../lean/V2Problems.lean) so that the fp64 enclosures equal realfp's
   for finite endpoints and a GPU certificate is accepted by the Lean checker as is.

   Soundness of the search itself (needed only for the "weaker than proof" uses): every
   operation encloses the real result -- directed rounding on every endpoint; mul takes the
   min/max of the four corner products rounded down/up; inv/div return the whole line when the
   divisor contains 0; sqrt clamps negative lower ends to 0 (realfp's sqrtI, sqrt x = 0 for x<0);
   any NaN in a result is caught by the comparisons (a NaN bound never accepts a box).
   fp32: box endpoints -1 + c 2^(1-s) are exact in binary32 for s <= 23 (checked by the
   driver: deeper boxes are reported unresolved); constants must be exactly representable
   in binary32 (checked at start-up). */
#ifndef MB2_H
#define MB2_H
#include <stdint.h>
#include <stddef.h>

#ifdef __CUDACC__
#define MBQ __host__ __device__ __forceinline__
#else
#define MBQ static inline
#endif

#define MB2_MAXD 10

template <class T> struct IV { T lo, hi; };

/* R: rounding policy with T and the directed operations. */
template <class R> MBQ IV<typename R::T> ivc(double c) { IV<typename R::T> r = {(typename R::T)c, (typename R::T)c}; return r; }
template <class R> MBQ IV<typename R::T> ivadd(IV<typename R::T> a, IV<typename R::T> b) {
  IV<typename R::T> r = {R::add_d(a.lo, b.lo), R::add_u(a.hi, b.hi)}; return r; }
template <class R> MBQ IV<typename R::T> ivsub(IV<typename R::T> a, IV<typename R::T> b) {
  IV<typename R::T> r = {R::sub_d(a.lo, b.hi), R::sub_u(a.hi, b.lo)}; return r; }
template <class T> MBQ T mbmin(T a, T b) { return a < b ? a : b; }
template <class T> MBQ T mbmax(T a, T b) { return a > b ? a : b; }
template <class R> MBQ IV<typename R::T> ivmul(IV<typename R::T> x, IV<typename R::T> y) {
  typedef typename R::T T;
  T a = x.lo, b = x.hi, c = y.lo, d = y.hi;
  if (R::nonfinite(a) || R::nonfinite(b) || R::nonfinite(c) || R::nonfinite(d)) {
    IV<T> w = {-R::inf(), R::inf()}; return w;   /* sound; realfp may be tighter */
  }
  T lo = mbmin(mbmin(R::mul_d(a, c), R::mul_d(a, d)), mbmin(R::mul_d(b, c), R::mul_d(b, d)));
  T hi = mbmax(mbmax(R::mul_u(a, c), R::mul_u(a, d)), mbmax(R::mul_u(b, c), R::mul_u(b, d)));
  IV<T> r = {lo, hi}; return r;
}
template <class R> MBQ IV<typename R::T> ivneg(IV<typename R::T> a) { IV<typename R::T> r = {-a.hi, -a.lo}; return r; }
/* realfp pown, even n: endpoints of |x| raised by the same binary exponentiation as
   Interval64.ipow (acc := acc*b if odd, b := b^2), rounded down (low end) / up (high end). */
template <class R> MBQ typename R::T powpt(typename R::T f, unsigned n, int up) {
  typename R::T acc = 1, b = f;
  while (n) {
    if (n & 1) acc = up ? R::mul_u(acc, b) : R::mul_d(acc, b);
    n >>= 1;
    b = up ? R::mul_u(b, b) : R::mul_d(b, b);
  }
  return acc;
}
template <class R> MBQ IV<typename R::T> ivpow(IV<typename R::T> x, unsigned n) {
  typedef typename R::T T;
  if (n == 0) { IV<T> r = {1, 1}; return r; }
  if (n % 2 == 0) {
    T m = x.lo >= 0 ? x.lo : (x.hi <= 0 ? -x.hi : (T)0);
    T M = mbmax(-x.lo, x.hi);
    IV<T> r = {powpt<R>(m, n, 0), powpt<R>(M, n, 1)}; return r;
  }
  IV<T> r = x;                                   /* odd: repeated interval product (sound) */
  for (unsigned k = 1; k < n; k++) r = ivmul<R>(r, x);
  return r;
}
/* Interval64.inv / evalFE (.div a b) = a * inv b */
template <class R> MBQ IV<typename R::T> ivinv(IV<typename R::T> a) {
  typedef typename R::T T;
  if (a.lo <= 0 && 0 <= a.hi) { IV<T> w = {-R::inf(), R::inf()}; return w; }
  IV<T> r = {R::div_d(1, a.hi), R::div_u(1, a.lo)}; return r;
}
template <class R> MBQ IV<typename R::T> ivdiv(IV<typename R::T> a, IV<typename R::T> b) { return ivmul<R>(a, ivinv<R>(b)); }
/* KF.sqrtI */
template <class R> MBQ IV<typename R::T> ivsqrt(IV<typename R::T> a) {
  typedef typename R::T T;
  if (a.hi < 0) { IV<T> z = {0, 0}; return z; }
  T l = a.lo < 0 ? (T)0 : a.lo;
  IV<T> r = {R::sqrt_d(l), R::sqrt_u(a.hi)}; return r;
}

/* ---------------------------------------------------------------------------------------
   Problems on [-1,1]^d. upper = 1: claim f <= bound; upper = 0: claim f >= bound.     */
enum { MB_P1, MB_P2, MB_NES, MB_PM, MB_C6, MB_M6, MB_R8, MB_C8, MB_NPROB };
static const int MB2_DIM[MB_NPROB] = {2, 4, 3, 3, 6, 6, 8, 8};
#ifdef __CUDACC__
__host__ __device__
#endif
constexpr int mb2_dim(int p) {
  return p == MB_P1 ? 2 : p == MB_P2 ? 4 : (p == MB_NES || p == MB_PM) ? 3 : (p == MB_C6 || p == MB_M6) ? 6 : 8;
}
static const int MB2_UPPER[MB_NPROB] = {1, 0, 0, 1, 1, 0, 0, 1};
/* bound = base + sgn * delta (sgn = +1 for upper claims, -1 for lower) */
static const double MB2_BASE[MB_NPROB] = {2, 0, 1.5, 0, 6, 0, -8, 8};
static const char *const MB2_NAME[MB_NPROB] = {"P1", "P2", "NES", "PM", "C6", "M6", "R8", "C8"};

template <class R> MBQ IV<typename R::T> sq(IV<typename R::T> x) { return ivpow<R>(x, 2); }
/* T8(x) = (((128u - 256)u + 160)u - 32)u + 1, u = x^2 */
template <class R> MBQ IV<typename R::T> t8(IV<typename R::T> x) {
  IV<typename R::T> u = sq<R>(x);
  IV<typename R::T> h = ivsub<R>(ivmul<R>(ivc<R>(128), u), ivc<R>(256));
  h = ivadd<R>(ivmul<R>(h, u), ivc<R>(160));
  h = ivsub<R>(ivmul<R>(h, u), ivc<R>(32));
  return ivadd<R>(ivmul<R>(h, u), ivc<R>(1));
}
/* T4(x) = (8u - 8)u + 1, u = x^2 */
template <class R> MBQ IV<typename R::T> t4(IV<typename R::T> x) {
  IV<typename R::T> u = sq<R>(x);
  return ivadd<R>(ivmul<R>(ivsub<R>(ivmul<R>(ivc<R>(8), u), ivc<R>(8)), u), ivc<R>(1));
}

template <class R> MBQ IV<typename R::T> mb2_eval(int prob, const IV<typename R::T> *X) {
  typedef IV<typename R::T> I;
  switch (prob) {
  case MB_P1: return ivadd<R>(t8<R>(X[0]), t8<R>(X[1]));
  case MB_P2: {
    I x2 = sq<R>(X[0]), y2 = sq<R>(X[1]), z2 = sq<R>(X[2]);
    I s = ivadd<R>(ivadd<R>(ivadd<R>(ivmul<R>(x2, y2), ivmul<R>(y2, z2)), ivmul<R>(z2, x2)), ivpow<R>(X[3], 4));
    I t = ivmul<R>(ivmul<R>(ivc<R>(4), ivmul<R>(X[0], X[1])), ivmul<R>(X[2], X[3]));
    return ivsub<R>(s, t);
  }
  case MB_NES: {   /* Nesbitt, a = 2 + x etc. in [1,3]: a/(b+c) + b/(c+a) + c/(a+b) >= 3/2 */
    I a = ivadd<R>(ivc<R>(2), X[0]), b = ivadd<R>(ivc<R>(2), X[1]), c = ivadd<R>(ivc<R>(2), X[2]);
    return ivadd<R>(ivadd<R>(ivdiv<R>(a, ivadd<R>(b, c)), ivdiv<R>(b, ivadd<R>(c, a))), ivdiv<R>(c, ivadd<R>(a, b)));
  }
  case MB_PM: {    /* power means: sqrt a + sqrt b + sqrt c - sqrt(3 (a + b + c)) <= 0 */
    I a = ivadd<R>(ivc<R>(2), X[0]), b = ivadd<R>(ivc<R>(2), X[1]), c = ivadd<R>(ivc<R>(2), X[2]);
    I s = ivadd<R>(ivadd<R>(ivsqrt<R>(a), ivsqrt<R>(b)), ivsqrt<R>(c));
    return ivsub<R>(s, ivsqrt<R>(ivmul<R>(ivc<R>(3), ivadd<R>(ivadd<R>(a, b), c))));
  }
  case MB_C6: case MB_C8: {  /* sum of T8(x_i) <= d (Chebyshev; max d at 9^d points) */
    int d = prob == MB_C6 ? 6 : 8;
    I s = t8<R>(X[0]);
    for (int i = 1; i < d; i++) s = ivadd<R>(s, t8<R>(X[i]));
    return s;
  }
  case MB_M6: {    /* Reznick's AM-GM (Motzkin-type) form, n = 6:
                      x6^12 + P (x1^2+...+x5^2) - 6 x6^2 P >= 0, P = x1^2 ... x5^2 */
    I p[5];
    for (int i = 0; i < 5; i++) p[i] = sq<R>(X[i]);
    I P = p[0], S = p[0];
    for (int i = 1; i < 5; i++) { P = ivmul<R>(P, p[i]); S = ivadd<R>(S, p[i]); }
    I A = ivadd<R>(ivpow<R>(X[5], 12), ivmul<R>(P, S));
    return ivsub<R>(A, ivmul<R>(ivmul<R>(ivc<R>(6), sq<R>(X[5])), P));
  }
  case MB_R8: {    /* ring of 8 Chebyshev "spins": sum_i T4(x_i) T4(x_{i+1 mod 8}) >= -8
                      (min -8 at the 2 * 3^4 * 2^4 alternating points T4 = +-1) */
    I t[8];
    for (int i = 0; i < 8; i++) t[i] = t4<R>(X[i]);
    I s = ivmul<R>(t[0], t[1]);
    for (int i = 1; i < 8; i++) s = ivadd<R>(s, ivmul<R>(t[i], t[(i + 1) % 8]));
    return s;
  }
  }
  I z = {0, 0}; return z;
}
/* Constants used above (checked exact in binary32 at start-up). */
static const double MB2_CONSTS[] = {128, 256, 160, 32, 1, 8, 2, 4, 3, 6};
#endif
