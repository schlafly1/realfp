/* realfp-grid: interval operations, templated over a directed-rounding policy P.
   They mirror realfp's checker (RealFPMathlib/c/grid_tape.c, i.e. Interval64.add / mul / pown /
   inv / sqrtI ...) operation by operation. With an exact policy (CUDA __dadd_rd..., or realfp's
   iv64r_* RN+error kernels on the CPU) the results are bit-identical to the checker's, so a
   certificate found in fp64 is accepted by the checker. With fp32 the enclosures are sound but
   wider; a box accepted in fp32 is (except in degenerate cases such as sqrt of an interval that
   is negative in fp64 but not in fp32) accepted in fp64 too. Nothing here is trusted: every
   certificate is re-checked by Lean (native_decide + the C checker). */
#pragma once
#ifdef __CUDACC_RTC__
typedef unsigned int uint32_t;
typedef unsigned long long uint64_t;
typedef unsigned char uint8_t;
#else
#include <stdint.h>
#endif
#ifdef __CUDACC__
#define HD __host__ __device__ __forceinline__
#else
#define HD inline
#endif

template <class T> struct IVT { T lo, hi; };

template <class T> HD bool isn_(T x) { return x != x; }
template <class T> HD bool isinf_(T x) { return x - x != x - x && x == x; }

template <class P> HD IVT<typename P::T> iv_invalid() {
  typename P::T n = P::nan(); IVT<typename P::T> r = {n, n}; return r;
}
template <class P> HD IVT<typename P::T> iv_whole() {
  IVT<typename P::T> r = {-P::inf(), P::inf()}; return r;
}
template <class T> HD bool anynan(IVT<T> a, IVT<T> b) {
  return isn_(a.lo) || isn_(a.hi) || isn_(b.lo) || isn_(b.hi);
}
template <class P> HD IVT<typename P::T> iv_add(IVT<typename P::T> a, IVT<typename P::T> b) {
  if (anynan(a, b)) return iv_invalid<P>();
  IVT<typename P::T> r = {P::add_d(a.lo, b.lo), P::add_u(a.hi, b.hi)}; return r;
}
template <class P> HD IVT<typename P::T> iv_sub(IVT<typename P::T> a, IVT<typename P::T> b) {
  if (anynan(a, b)) return iv_invalid<P>();
  IVT<typename P::T> r = {P::sub_d(a.lo, b.hi), P::sub_u(a.hi, b.lo)}; return r;
}
template <class P> HD void acc_corner(typename P::T x, typename P::T y, typename P::T &lo,
                                      typename P::T &hi, int &got) {
  if ((x == 0 && isinf_(y)) || (y == 0 && isinf_(x))) return;
  typename P::T d = P::mul_d(x, y), u = P::mul_u(x, y);
  if (isn_(d) || isn_(u)) return;
  if (!got) { lo = d; hi = u; got = 1; return; }
  lo = (d < lo) ? d : lo;
  hi = (u > hi) ? u : hi;
}
template <class P> HD IVT<typename P::T> iv_mul(IVT<typename P::T> a, IVT<typename P::T> b) {
  if (anynan(a, b)) return iv_invalid<P>();
  typename P::T lo = 0, hi = 0; int got = 0;
  acc_corner<P>(a.lo, b.lo, lo, hi, got);
  acc_corner<P>(a.lo, b.hi, lo, hi, got);
  acc_corner<P>(a.hi, b.lo, lo, hi, got);
  acc_corner<P>(a.hi, b.hi, lo, hi, got);
  if (!got) return iv_whole<P>();
  IVT<typename P::T> r = {lo, hi}; return r;
}
template <class T> HD IVT<T> iv_neg(IVT<T> a) { IVT<T> r = {-a.hi, -a.lo}; return r; }
template <class T> HD T fmax_l(T x, T y) { return (x > y) ? x : y; }
template <class T> HD T fmin_l(T x, T y) { return (x < y) ? x : y; }
template <class P> HD IVT<typename P::T> iv_abs(IVT<typename P::T> a) {
  typedef typename P::T T;
  if (isn_(a.lo) || isn_(a.hi)) return iv_invalid<P>();
  if (0 <= a.lo) return a;
  if (a.hi <= 0) { IVT<T> r = {-a.hi, -a.lo}; return r; }
  IVT<T> r = {(T)0, fmax_l(-a.lo, a.hi)}; return r;
}
template <class P> HD IVT<typename P::T> iv_square(IVT<typename P::T> a) {
  typedef typename P::T T;
  if (isn_(a.lo) || isn_(a.hi)) return iv_invalid<P>();
  if (0 <= a.lo) { IVT<T> r = {P::mul_d(a.lo, a.lo), P::mul_u(a.hi, a.hi)}; return r; }
  if (a.hi <= 0) { IVT<T> r = {P::mul_d(a.hi, a.hi), P::mul_u(a.lo, a.lo)}; return r; }
  IVT<T> r = {(T)0, fmax_l(P::mul_u(a.lo, a.lo), P::mul_u(a.hi, a.hi))}; return r;
}
template <class P> HD IVT<typename P::T> iv_ipow(IVT<typename P::T> b, uint32_t e) {
  typedef typename P::T T;
  IVT<T> acc = {(T)1, (T)1};
  for (int fuel = 64; fuel > 0; fuel--) {
    if (e == 0) return acc;
    IVT<T> nb = iv_square<P>(b);
    if (e % 2 == 1) acc = iv_mul<P>(acc, b);
    b = nb; e /= 2;
  }
  if (e == 0) return acc;
  return iv_whole<P>();
}
template <class P> HD typename P::T pow_lo(typename P::T f, uint32_t n) {
  if (isinf_(f)) return f; IVT<typename P::T> p = {f, f}; return iv_ipow<P>(p, n).lo;
}
template <class P> HD typename P::T pow_hi(typename P::T f, uint32_t n) {
  if (isinf_(f)) return f; IVT<typename P::T> p = {f, f}; return iv_ipow<P>(p, n).hi;
}
template <class P> HD IVT<typename P::T> iv_pown(IVT<typename P::T> a, uint32_t n) {
  typedef typename P::T T;
  if (isn_(a.lo) || isn_(a.hi)) return iv_invalid<P>();
  if (n == 0) { IVT<T> r = {(T)1, (T)1}; return r; }
  if (n % 2 == 1) { IVT<T> r = {pow_lo<P>(a.lo, n), pow_hi<P>(a.hi, n)}; return r; }
  IVT<T> b = iv_abs<P>(a);
  IVT<T> r = {pow_lo<P>(b.lo, n), pow_hi<P>(b.hi, n)}; return r;
}
template <class T> HD bool contains_zero(IVT<T> a) {
  return !(isn_(a.lo) || isn_(a.hi)) && a.lo <= 0 && 0 <= a.hi;
}
template <class P> HD IVT<typename P::T> iv_inv(IVT<typename P::T> a) {
  typedef typename P::T T;
  if (isn_(a.lo) || isn_(a.hi)) return iv_invalid<P>();
  if (contains_zero(a)) return iv_whole<P>();
  IVT<T> r = {P::div_d((T)1, a.hi), P::div_u((T)1, a.lo)}; return r;
}
template <class P> HD IVT<typename P::T> iv_sqrt(IVT<typename P::T> a) {
  typedef typename P::T T;
  if (isn_(a.lo) || isn_(a.hi)) return iv_invalid<P>();
  if (a.hi < 0) return iv_invalid<P>();
  T l = (a.lo < 0) ? (T)0 : a.lo;
  IVT<T> r = {P::sqrt_d(l), P::sqrt_u(a.hi)}; return r;
}
template <class T> HD IVT<T> iv_hull(IVT<T> a, IVT<T> b) {
  if (isn_(a.lo) || isn_(a.hi)) return b;
  if (isn_(b.lo) || isn_(b.hi)) return a;
  IVT<T> r = {fmin_l(a.lo, b.lo), fmax_l(a.hi, b.hi)}; return r;
}
template <class P> HD IVT<typename P::T> iv_sqrtI(IVT<typename P::T> a) {
  typedef typename P::T T;
  if (a.lo < 0) { IVT<T> z = {(T)0, (T)0}; return iv_hull(z, iv_sqrt<P>(a)); }
  return iv_sqrt<P>(a);
}

/* evalFE on the tape: X = variables (d of them), K = constants, R = registers (n). */
template <class P>
HD IVT<typename P::T> tape_eval(const uint32_t *code, uint32_t n, const IVT<typename P::T> *K,
                                 const IVT<typename P::T> *X, uint32_t d, IVT<typename P::T> *R) {
  typedef typename P::T T;
  for (uint32_t k = 0; k < n; k++) {
    uint32_t op = code[3 * k], a = code[3 * k + 1], b = code[3 * k + 2];
    switch (op) {
      case 0: { IVT<T> z = {(T)0, (T)0}; R[k] = a < d ? X[a] : z; break; }
      case 1: R[k] = K[a]; break;
      case 2: R[k] = iv_add<P>(R[a], R[b]); break;
      case 3: R[k] = iv_sub<P>(R[a], R[b]); break;
      case 4: R[k] = iv_mul<P>(R[a], R[b]); break;
      case 5: R[k] = iv_neg(R[a]); break;
      case 6: R[k] = iv_pown<P>(R[a], b); break;
      case 7: R[k] = iv_mul<P>(R[a], iv_inv<P>(R[b])); break;
      case 8: R[k] = iv_sqrtI<P>(R[a]); break;
      default: R[k] = iv_invalid<P>(); break;
    }
  }
  return R[n - 1];
}

/* midF lo hi = lo * 0.5 + hi * 0.5 in binary64 round-to-nearest (RealFPGridNative/Basic.lean). */
#ifdef __CUDACC__
__host__ __device__ __forceinline__ double midF(double lo, double hi) {
#ifdef __CUDA_ARCH__
  return __dadd_rn(__dmul_rn(lo, 0.5), __dmul_rn(hi, 0.5));
#else
  volatile double a = lo * 0.5, b = hi * 0.5; return a + b;
#endif
}
#else
inline double midF(double lo, double hi) { volatile double a = lo * 0.5, b = hi * 0.5; return a + b; }
#endif
