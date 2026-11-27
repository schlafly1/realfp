/* realfp-grid GPU rounding policies and kernel parameters; shared by gpu.cu and the kernels
   compiled at run time (NVRTC, gpu.cu: jit_source). */
#pragma once
#include "ops.hpp"

struct G64 {
  typedef double T;
  static __device__ __forceinline__ double add_d(double a, double b) { return __dadd_rd(a, b); }
  static __device__ __forceinline__ double add_u(double a, double b) { return __dadd_ru(a, b); }
  static __device__ __forceinline__ double sub_d(double a, double b) { return __dsub_rd(a, b); }
  static __device__ __forceinline__ double sub_u(double a, double b) { return __dsub_ru(a, b); }
  static __device__ __forceinline__ double mul_d(double a, double b) { return __dmul_rd(a, b); }
  static __device__ __forceinline__ double mul_u(double a, double b) { return __dmul_ru(a, b); }
  static __device__ __forceinline__ double div_d(double a, double b) { return __ddiv_rd(a, b); }
  static __device__ __forceinline__ double div_u(double a, double b) { return __ddiv_ru(a, b); }
  static __device__ __forceinline__ double sqrt_d(double a) { return __dsqrt_rd(a); }
  static __device__ __forceinline__ double sqrt_u(double a) { return __dsqrt_ru(a); }
  static __device__ __forceinline__ double inf() { return __longlong_as_double(0x7ff0000000000000ll); }
  static __device__ __forceinline__ double nan() { return __longlong_as_double(0x7ff8000000000000ll); }
  static __device__ __forceinline__ double lo_of(double x) { return x; }
  static __device__ __forceinline__ double hi_of(double x) { return x; }
};
struct G32 {
  typedef float T;
  static __device__ __forceinline__ float add_d(float a, float b) { return __fadd_rd(a, b); }
  static __device__ __forceinline__ float add_u(float a, float b) { return __fadd_ru(a, b); }
  static __device__ __forceinline__ float sub_d(float a, float b) { return __fsub_rd(a, b); }
  static __device__ __forceinline__ float sub_u(float a, float b) { return __fsub_ru(a, b); }
  static __device__ __forceinline__ float mul_d(float a, float b) { return __fmul_rd(a, b); }
  static __device__ __forceinline__ float mul_u(float a, float b) { return __fmul_ru(a, b); }
  static __device__ __forceinline__ float div_d(float a, float b) { return __fdiv_rd(a, b); }
  static __device__ __forceinline__ float div_u(float a, float b) { return __fdiv_ru(a, b); }
  static __device__ __forceinline__ float sqrt_d(float a) { return __fsqrt_rd(a); }
  static __device__ __forceinline__ float sqrt_u(float a) { return __fsqrt_ru(a); }
  static __device__ __forceinline__ float inf() { return __int_as_float(0x7f800000); }
  static __device__ __forceinline__ float nan() { return __int_as_float(0x7fc00000); }
  static __device__ __forceinline__ float lo_of(double x) { return __double2float_rd(x); }
  static __device__ __forceinline__ float hi_of(double x) { return __double2float_ru(x); }
};

struct Par { uint32_t d, n; int upper; double c; float c32; };

/* the leaf test (as the checker's gLe / gGe; NaN fails) */
template <class R>
__device__ __forceinline__ bool leaf_ok(const Par &p, IVT<typename R::T> F) {
  if (isn_(F.lo) || isn_(F.hi)) return false;
  if (sizeof(typename R::T) == 4) return p.upper ? ((float)F.hi <= p.c32) : (p.c32 <= (float)F.lo);
  return p.upper ? ((double)F.hi <= p.c) : (p.c <= (double)F.lo);
}

template <class R>
__device__ __forceinline__ IVT<typename R::T> load_var(const double *box, uint64_t n, uint64_t i, uint32_t j, bool point) {
  double lo = box[(2 * j) * n + i], hi = box[(2 * j + 1) * n + i];
  if (point) { double m = midF(lo, hi); lo = m; hi = m; }
  IVT<typename R::T> r = {R::lo_of(lo), R::hi_of(hi)}; return r;
}
