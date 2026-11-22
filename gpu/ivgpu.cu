/* Interval64 GPU kernels: the expressions of ivexpr.h compiled with CUDA's
   per-instruction directed-rounding intrinsics (no rounding-mode state).
   Host API (extern "C") is in ivgpu.h; used by bench.cu and by the Lean FFI shim. */
#include <cuda_runtime.h>
#include <math.h>
#include <stdio.h>
#include <stdint.h>
#include "bench_common.h"
#include "ivgpu.h"

#define IVQ static __device__ __forceinline__
#define IVT double
#define IVN(n) n##_d
#define ADD_D __dadd_rd
#define ADD_U __dadd_ru
#define SUB_D __dsub_rd
#define SUB_U __dsub_ru
#define MUL_D __dmul_rd
#define MUL_U __dmul_ru
#define DIV_D __ddiv_rd
#define DIV_U __ddiv_ru
#define SQRT_D __dsqrt_rd
#define SQRT_U __dsqrt_ru
#include "ivexpr.h"
#undef IVT
#undef IVN
#undef ADD_D
#undef ADD_U
#undef SUB_D
#undef SUB_U
#undef MUL_D
#undef MUL_U
#undef DIV_D
#undef DIV_U
#undef SQRT_D
#undef SQRT_U
#undef IV_MIN
#undef IV_MAX
/* fp32 contrast version (NOT Interval64: binary32 endpoints). */
#define IVT float
#define IVN(n) n##_f
#define ADD_D __fadd_rd
#define ADD_U __fadd_ru
#define SUB_D __fsub_rd
#define SUB_U __fsub_ru
#define MUL_D __fmul_rd
#define MUL_U __fmul_ru
#define DIV_D __fdiv_rd
#define DIV_U __fdiv_ru
#define SQRT_D __fsqrt_rd
#define SQRT_U __fsqrt_ru
#include "ivexpr.h"

__constant__ double c_R[2], c_bound[2];
__constant__ int c_upper[2];

static __device__ __forceinline__ iv_d eval(int fn, iv_d X, iv_d Y) { return iv_eval_d(fn, X, Y); }
static __device__ __forceinline__ iv_f eval(int fn, iv_f X, iv_f Y) { return iv_eval_f(fn, X, Y); }

#define TPB 256
#define MAXBLK 4096

static __device__ __forceinline__ iv_d mk(double l, double h) { iv_d r = {l, h}; return r; }
static __device__ __forceinline__ iv_f mk(float l, float h) { iv_f r = {l, h}; return r; }

static __device__ __forceinline__ void block_reduce(double mn, double mx, unsigned long long fails,
    double *p_min, double *p_max, unsigned long long *p_fail) {
  for (int o = 16; o > 0; o >>= 1) {
    double a = __shfl_down_sync(0xffffffffu, mn, o), b = __shfl_down_sync(0xffffffffu, mx, o);
    unsigned long long c = __shfl_down_sync(0xffffffffu, fails, o);
    mn = IV_MIN(mn, a); mx = IV_MAX(mx, b); fails += c;
  }
  __shared__ double smn[TPB / 32], smx[TPB / 32];
  __shared__ unsigned long long sf[TPB / 32];
  int w = threadIdx.x >> 5, l = threadIdx.x & 31;
  if (l == 0) { smn[w] = mn; smx[w] = mx; sf[w] = fails; }
  __syncthreads();
  if (threadIdx.x == 0) {
    for (int q = 1; q < TPB / 32; q++) { mn = IV_MIN(mn, smn[q]); mx = IV_MAX(mx, smx[q]); fails += sf[q]; }
    p_min[blockIdx.x] = mn; p_max[blockIdx.x] = mx; p_fail[blockIdx.x] = fails;
  }
}

/* One thread per box (grid-stride). Box idx = j*n + i, x in [-R+i h, -R+(i+1) h]. */
template <typename T, bool STORE>
__global__ void __launch_bounds__(TPB) k_grid(int fn, int k, T *lo_out, T *hi_out,
                       double *p_min, double *p_max, unsigned long long *p_fail) {
  const uint64_t n = 1ull << k, N = n * n;
  const T R = (T)c_R[fn], h = (T)(2 * c_R[fn]) / (T)n;   /* exact: powers of 2 */
  const double bound = c_bound[fn];
  const int upper = c_upper[fn];
  double mn = INFINITY, mx = -INFINITY;
  unsigned long long fails = 0;
  for (uint64_t idx = blockIdx.x * (uint64_t)blockDim.x + threadIdx.x; idx < N;
       idx += (uint64_t)gridDim.x * blockDim.x) {
    uint64_t i = idx & (n - 1), j = idx >> k;
    /* exact in any evaluation order / contraction (i < 2^26, h a power of 2) */
    auto X = mk(-R + (T)i * h, -R + (T)(i + 1) * h);
    auto Y = mk(-R + (T)j * h, -R + (T)(j + 1) * h);
    auto F = eval(fn, X, Y);
    double lo = (double)F.lo, hi = (double)F.hi;
    mn = IV_MIN(mn, lo); mx = IV_MAX(mx, hi);
    fails += upper ? !(hi <= bound) : !(lo >= bound);
    if (STORE) { lo_out[idx] = F.lo; hi_out[idx] = F.hi; }
  }
  block_reduce(mn, mx, fails, p_min, p_max, p_fail);
}

/* Arbitrary box list: boxes[4b..4b+3] = xlo, xhi, ylo, yhi -> out[2b], out[2b+1]. */
__global__ void __launch_bounds__(TPB) k_list(int fn, const double *boxes, uint64_t N, double *out) {
  for (uint64_t b = blockIdx.x * (uint64_t)blockDim.x + threadIdx.x; b < N;
       b += (uint64_t)gridDim.x * blockDim.x) {
    double4_32a q = reinterpret_cast<const double4_32a *>(boxes)[b];
    iv_d F = iv_eval_d(fn, mk(q.x, q.y), mk(q.z, q.w));
    reinterpret_cast<double2 *>(out)[b] = make_double2(F.lo, F.hi);
  }
}

/* ---------------- host side ---------------- */
#define CK(x) do { cudaError_t e_ = (x); if (e_ != cudaSuccess) { \
  fprintf(stderr, "CUDA error %s at %s:%d\n", cudaGetErrorString(e_), __FILE__, __LINE__); return -1; } } while (0)

static int g_init = 0, g_sms = 0;
static double *d_min, *d_max, *h_min, *h_max;
static unsigned long long *d_fail, *h_fail;
static void *d_a = 0, *d_b = 0; static size_t d_cap = 0;   /* store / list buffers */
static cudaEvent_t e0, e1;

extern "C" int ivgpu_init(void) {
  if (g_init) return 0;
  CK(cudaSetDevice(0));
  cudaDeviceProp p; CK(cudaGetDeviceProperties(&p, 0)); g_sms = p.multiProcessorCount;
  CK(cudaMemcpyToSymbol(c_R, FN_R, sizeof FN_R));
  CK(cudaMemcpyToSymbol(c_bound, FN_BOUND, sizeof FN_BOUND));
  CK(cudaMemcpyToSymbol(c_upper, FN_UPPER, sizeof FN_UPPER));
  CK(cudaMalloc(&d_min, MAXBLK * 8)); CK(cudaMalloc(&d_max, MAXBLK * 8)); CK(cudaMalloc(&d_fail, MAXBLK * 8));
  CK(cudaMallocHost(&h_min, MAXBLK * 8)); CK(cudaMallocHost(&h_max, MAXBLK * 8)); CK(cudaMallocHost(&h_fail, MAXBLK * 8));
  CK(cudaEventCreate(&e0)); CK(cudaEventCreate(&e1));
  CK(cudaFree(0));
  g_init = 1; return 0;
}

extern "C" int ivgpu_info(char *name, int len, int *sms, int *cc_major, int *cc_minor) {
  cudaDeviceProp p; CK(cudaGetDeviceProperties(&p, 0));
  snprintf(name, len, "%s", p.name); *sms = p.multiProcessorCount; *cc_major = p.major; *cc_minor = p.minor;
  return 0;
}

static int ensure(size_t bytes) {
  if (bytes <= d_cap) return 0;
  if (d_a) { cudaFree(d_a); cudaFree(d_b); }
  CK(cudaMalloc(&d_a, bytes)); CK(cudaMalloc(&d_b, bytes)); d_cap = bytes; return 0;
}

static int nblocks(uint64_t N) {
  uint64_t want = (N + TPB - 1) / TPB, cap = (uint64_t)g_sms * 16;
  if (cap > MAXBLK) cap = MAXBLK;
  return (int)(want < cap ? want : cap);
}

static int finish_reduce(int nb, red_t *r) {
  CK(cudaMemcpy(h_min, d_min, nb * 8, cudaMemcpyDeviceToHost));
  CK(cudaMemcpy(h_max, d_max, nb * 8, cudaMemcpyDeviceToHost));
  CK(cudaMemcpy(h_fail, d_fail, nb * 8, cudaMemcpyDeviceToHost));
  red_t t = {INFINITY, -INFINITY, 0};
  for (int b = 0; b < nb; b++) { t.minlo = IV_MIN(t.minlo, h_min[b]); t.maxhi = IV_MAX(t.maxhi, h_max[b]); t.fails += h_fail[b]; }
  *r = t; return 0;
}

/* Grid reduce: fn, 2^k x 2^k boxes, prec 64 or 32. kernel_ms: device time of the kernel. */
extern "C" int ivgpu_grid(int fn, int k, int prec, red_t *r, float *kernel_ms) {
  if (ivgpu_init()) return -1;
  uint64_t N = 1ull << (2 * k); int nb = nblocks(N);
  CK(cudaEventRecord(e0));
  if (prec == 32) k_grid<float, false><<<nb, TPB>>>(fn, k, 0, 0, d_min, d_max, d_fail);
  else k_grid<double, false><<<nb, TPB>>>(fn, k, 0, 0, d_min, d_max, d_fail);
  CK(cudaGetLastError());
  CK(cudaEventRecord(e1)); CK(cudaEventSynchronize(e1));
  if (kernel_ms) CK(cudaEventElapsedTime(kernel_ms, e0, e1));
  return finish_reduce(nb, r);
}

/* Grid with every box's endpoints copied back (lo/hi: N doubles, or N floats if prec 32). */
extern "C" int ivgpu_grid_store(int fn, int k, int prec, void *lo, void *hi, red_t *r) {
  if (ivgpu_init()) return -1;
  uint64_t N = 1ull << (2 * k); int nb = nblocks(N); size_t es = prec == 32 ? 4 : 8;
  if (ensure(N * es)) return -1;
  if (prec == 32) k_grid<float, true><<<nb, TPB>>>(fn, k, (float *)d_a, (float *)d_b, d_min, d_max, d_fail);
  else k_grid<double, true><<<nb, TPB>>>(fn, k, (double *)d_a, (double *)d_b, d_min, d_max, d_fail);
  CK(cudaGetLastError()); CK(cudaDeviceSynchronize());
  CK(cudaMemcpy(lo, d_a, N * es, cudaMemcpyDeviceToHost));
  CK(cudaMemcpy(hi, d_b, N * es, cudaMemcpyDeviceToHost));
  return finish_reduce(nb, r);
}

/* Box list: host boxes (4N doubles) -> host out (2N doubles). Includes both copies.
   kernel_ms: device time of the kernel alone. */
extern "C" int ivgpu_list(int fn, const double *boxes, uint64_t N, double *out, float *kernel_ms) {
  if (ivgpu_init()) return -1;
  if (N == 0) return 0;
  if (ensure(N * 32)) return -1;
  CK(cudaMemcpyAsync(d_a, boxes, N * 32, cudaMemcpyHostToDevice));
  CK(cudaEventRecord(e0));
  k_list<<<nblocks(N), TPB>>>(fn, (const double *)d_a, N, (double *)d_b);
  CK(cudaGetLastError());
  CK(cudaEventRecord(e1));
  CK(cudaMemcpyAsync(out, d_b, N * 16, cudaMemcpyDeviceToHost));
  CK(cudaDeviceSynchronize());
  if (kernel_ms) CK(cudaEventElapsedTime(kernel_ms, e0, e1));
  return 0;
}

extern "C" void *ivgpu_host_alloc(size_t bytes) { void *p = 0; return cudaMallocHost(&p, bytes) == cudaSuccess ? p : 0; }
extern "C" void ivgpu_host_free(void *p) { cudaFreeHost(p); }
