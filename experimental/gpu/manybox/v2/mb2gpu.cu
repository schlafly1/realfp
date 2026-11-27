/* manybox v2 GPU engine: level-synchronous bisection of a forest of boxes, fp64 or fp32 with
   CUDA's per-instruction directed rounding; memory-capped (a level larger than `cap` is
   processed in chunks, depth first). Per level: eval kernel -> CUB scan -> children. */
#include <cuda_runtime.h>
#include <cub/cub.cuh>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "mb2.hpp"

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
  static __device__ __forceinline__ bool nonfinite(double a) { return !isfinite(a); }
  static __device__ __forceinline__ double inf() { return __longlong_as_double(0x7ff0000000000000ll); }
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
  static __device__ __forceinline__ bool nonfinite(float a) { return !isfinite(a); }
  static __device__ __forceinline__ float inf() { return __int_as_float(0x7f800000); }
};

#define TPB 256
#define CK(x) do { cudaError_t e_ = (x); if (e_ != cudaSuccess) { \
  fprintf(stderr, "CUDA error %s at %s:%d\n", cudaGetErrorString(e_), __FILE__, __LINE__); exit(2); } } while (0)

struct Coords { uint32_t *c[MB2_MAXD]; };
struct Ref { unsigned long long cnt; unsigned long long first; };

/* flag: 1 = split, 0 = leaf (claim proved on the box); refuted boxes (claim false on the whole
   box) are counted and also flagged 1 (the driver stops at the first refutation). */
template <class R, int PROB>
__global__ void __launch_bounds__(TPB) k_eval(int level, uint64_t n, Coords A, double bound, int upper,
                                              uint32_t *fl, Ref *ref) {
  constexpr int d = mb2_dim(PROB);
  uint64_t i = blockIdx.x * (uint64_t)blockDim.x + threadIdx.x;
  if (i >= n) return;
  typedef typename R::T T;
  IV<T> X[MB2_MAXD];
#pragma unroll
  for (int j = 0; j < d; j++) {
    double h = ldexp(2.0, -((level + d - 1 - j) / d));
    double c = (double)A.c[j][i];
    X[j].lo = (T)__dadd_rn(-1.0, __dmul_rn(c, h));          /* exact (driver limits depth) */
    X[j].hi = (T)__dadd_rn(-1.0, __dmul_rn(__dadd_rn(c, 1.0), h));
  }
  IV<T> F = mb2_eval<R>(PROB, X);
  double lo = (double)F.lo, hi = (double)F.hi;
  uint32_t f; bool rf;
  if (upper) { f = !(hi <= bound); rf = lo > bound; }
  else { f = !(lo >= bound); rf = hi < bound; }
  fl[i] = f;
  if (rf) { atomicAdd(&ref->cnt, 1ull); atomicMin(&ref->first, (unsigned long long)i); }
}

__global__ void k_children(int d, int sd, uint64_t n, Coords A, Coords B, const uint32_t *fl, const uint32_t *off) {
  uint64_t i = blockIdx.x * (uint64_t)blockDim.x + threadIdx.x;
  if (i >= n || !fl[i]) return;
  uint64_t o = 2ull * off[i];
  for (int j = 0; j < d; j++) {
    uint32_t c = A.c[j][i];
    if (j == sd) { B.c[j][o] = 2 * c; B.c[j][o + 1] = 2 * c + 1; }
    else { B.c[j][o] = c; B.c[j][o + 1] = c; }
  }
}
__global__ void k_compact(int d, uint64_t n, Coords A, Coords P, const uint32_t *fl, const uint32_t *off) {
  uint64_t i = blockIdx.x * (uint64_t)blockDim.x + threadIdx.x;
  if (i >= n || !fl[i]) return;
  for (int j = 0; j < d; j++) P.c[j][off[i]] = A.c[j][i];
}
/* children of parents P[a .. a+m) into B[0 .. 2m) */
__global__ void k_kids(int d, int sd, uint64_t a, uint64_t m, Coords P, Coords B) {
  uint64_t k = blockIdx.x * (uint64_t)blockDim.x + threadIdx.x;
  if (k >= m) return;
  for (int j = 0; j < d; j++) {
    uint32_t c = P.c[j][a + k];
    if (j == sd) { B.c[j][2 * k] = 2 * c; B.c[j][2 * k + 1] = 2 * c + 1; }
    else { B.c[j][2 * k] = c; B.c[j][2 * k + 1] = c; }
  }
}
__global__ void k_pack(uint64_t n, const uint32_t *fl, uint8_t *out) {
  uint64_t i = blockIdx.x * (uint64_t)blockDim.x + threadIdx.x;
  if (i < n) out[i] = (uint8_t)fl[i];
}

static uint32_t *dA[MB2_MAXD], *dB[MB2_MAXD], *dfl, *doff, *hcnt;
static uint8_t *dpk;
static Ref *dref, *href;
static void *dtmp; static size_t tmpcap, cap_alloc;
static int inited;

static void ensure(size_t need) {
  if (need <= cap_alloc) return;
  size_t nc = cap_alloc ? cap_alloc : 1 << 16; while (nc < need) nc *= 2;
  for (int j = 0; j < MB2_MAXD; j++) {
    if (dA[j]) { CK(cudaFree(dA[j])); CK(cudaFree(dB[j])); }
    CK(cudaMalloc(&dA[j], nc * 4)); CK(cudaMalloc(&dB[j], nc * 4));
  }
  if (dfl) { CK(cudaFree(dfl)); CK(cudaFree(doff)); CK(cudaFree(dpk)); }
  CK(cudaMalloc(&dfl, nc * 4)); CK(cudaMalloc(&doff, nc * 4)); CK(cudaMalloc(&dpk, nc));
  size_t t = 0; cub::DeviceScan::ExclusiveSum(NULL, t, dfl, doff, (int)nc);
  if (t > tmpcap) { if (dtmp) CK(cudaFree(dtmp)); CK(cudaMalloc(&dtmp, t)); tmpcap = t; }
  cap_alloc = nc;
}

extern "C++" int mb2_gpu_init(char *name, int len) {
  if (!inited) {
    CK(cudaSetDevice(0)); CK(cudaFree(0));
    CK(cudaMallocHost(&hcnt, 16)); CK(cudaMalloc(&dref, sizeof(Ref))); CK(cudaMallocHost(&href, sizeof(Ref)));
    ensure(1 << 20);
    inited = 1;
  }
  cudaDeviceProp p; CK(cudaGetDeviceProperties(&p, 0));
  if (name) snprintf(name, len, "%s, %d SMs, cc %d.%d", p.name, p.multiProcessorCount, p.major, p.minor);
  return 0;
}

template <class R>
static void launch_eval(int prob, unsigned nb, int level, uint64_t n, Coords A, double bound, int upper) {
#define L(P) case P: k_eval<R, P><<<nb, TPB>>>(level, n, A, bound, upper, dfl, dref); break;
  switch (prob) { L(MB_P1) L(MB_P2) L(MB_NES) L(MB_PM) L(MB_C6) L(MB_M6) L(MB_R8) L(MB_C8) }
#undef L
}

struct Ctx { const mb2_opts *o; mb2_stats *st; std::vector<uint8_t> *flags; int d, upper; uint64_t cap; };

static Coords cur(uint32_t **X) { Coords C; for (int j = 0; j < MB2_MAXD; j++) C.c[j] = X[j]; return C; }

/* BFS from the n boxes in dA at `level`. */
static void bfs(Ctx &x, int level, uint64_t n) {
  const mb2_opts &o = *x.o; mb2_stats &st = *x.st; int d = x.d;
  for (; n > 0; level++) {
    if (level + 1 > st.levels) st.levels = level + 1;
    if (level >= o.maxlevel) { st.unresolved += n; return; }
    st.evals += n; if (n > st.peak) st.peak = n;
    unsigned nb = (unsigned)((n + TPB - 1) / TPB);
    CK(cudaMemsetAsync(dref, 0, sizeof(Ref)));
    Ref init = {0ull, ~0ull}; CK(cudaMemcpyAsync(dref, &init, sizeof(Ref), cudaMemcpyHostToDevice));
    if (o.prec == 32) launch_eval<G32>(o.prob, nb, level, n, cur(dA), o.bound, x.upper);
    else launch_eval<G64>(o.prob, nb, level, n, cur(dA), o.bound, x.upper);
    size_t t = tmpcap;
    CK(cub::DeviceScan::ExclusiveSum(dtmp, t, dfl, doff, (int)n));
    CK(cudaMemcpyAsync(hcnt, doff + (n - 1), 4, cudaMemcpyDeviceToHost));
    CK(cudaMemcpyAsync(hcnt + 1, dfl + (n - 1), 4, cudaMemcpyDeviceToHost));
    CK(cudaMemcpyAsync(href, dref, sizeof(Ref), cudaMemcpyDeviceToHost));
    if (x.flags) k_pack<<<nb, TPB>>>(n, dfl, dpk);
    CK(cudaStreamSynchronize(0));
    if (x.flags) {
      size_t o0 = x.flags->size(); x.flags->resize(o0 + n);
      CK(cudaMemcpy(x.flags->data() + o0, dpk, n, cudaMemcpyDeviceToHost));
    }
    if (href->cnt) {
      if (st.refuted == 0) {
        st.ref_level = level;
        for (int j = 0; j < d; j++) CK(cudaMemcpy(&st.ref_c[j], dA[j] + href->first, 4, cudaMemcpyDeviceToHost));
      }
      st.refuted += href->cnt;
      return;                                         /* claim refuted: stop */
    }
    uint64_t nf = (uint64_t)hcnt[0] + hcnt[1];
    st.leaves += n - nf;
    if (nf == 0) return;
    int sd = level % d;
    if (2 * nf <= x.cap) {
      if (2 * nf > cap_alloc) {   /* grow, keeping this level */
        uint32_t *keep[MB2_MAXD], *kfl, *koff;
        for (int j = 0; j < d; j++) { CK(cudaMalloc(&keep[j], n * 4)); CK(cudaMemcpy(keep[j], dA[j], n * 4, cudaMemcpyDeviceToDevice)); }
        CK(cudaMalloc(&kfl, n * 4)); CK(cudaMalloc(&koff, n * 4));
        CK(cudaMemcpy(kfl, dfl, n * 4, cudaMemcpyDeviceToDevice)); CK(cudaMemcpy(koff, doff, n * 4, cudaMemcpyDeviceToDevice));
        ensure(2 * nf);
        for (int j = 0; j < d; j++) { CK(cudaMemcpy(dA[j], keep[j], n * 4, cudaMemcpyDeviceToDevice)); CK(cudaFree(keep[j])); }
        CK(cudaMemcpy(dfl, kfl, n * 4, cudaMemcpyDeviceToDevice)); CK(cudaMemcpy(doff, koff, n * 4, cudaMemcpyDeviceToDevice));
        CK(cudaFree(kfl)); CK(cudaFree(koff));
      }
      k_children<<<nb, TPB>>>(d, sd, n, cur(dA), cur(dB), dfl, doff);
      CK(cudaGetLastError());
      for (int j = 0; j < MB2_MAXD; j++) { uint32_t *tt = dA[j]; dA[j] = dB[j]; dB[j] = tt; }
      n = 2 * nf;
      continue;
    }
    if (x.flags) { st.ok = -1; return; }             /* certificate mode needs one pass */
    /* too wide: keep the nf parents aside, then go depth first over chunks of them */
    uint32_t *P[MB2_MAXD] = {0};
    for (int j = 0; j < d; j++) CK(cudaMalloc(&P[j], nf * 4));
    k_compact<<<nb, TPB>>>(d, n, cur(dA), cur(P), dfl, doff);
    CK(cudaGetLastError());
    uint64_t ch = x.cap / 2;
    for (uint64_t a = 0; a < nf; a += ch) {
      uint64_t m = nf - a < ch ? nf - a : ch;
      ensure(2 * m);
      k_kids<<<(unsigned)((m + TPB - 1) / TPB), TPB>>>(d, sd, a, m, cur(P), cur(dA));
      CK(cudaGetLastError());
      bfs(x, level + 1, 2 * m);
      if (st.refuted || st.ok < 0) break;
    }
    for (int j = 0; j < d; j++) CK(cudaFree(P[j]));
    return;
  }
}

mb2_stats mb2_gpu(const mb2_opts &o, const mb2_forest &f, std::vector<uint8_t> *flags) {
  mb2_gpu_init(NULL, 0);
  mb2_stats st; memset(&st, 0, sizeof st);
  int d = MB2_DIM[o.prob];
  Ctx x = {&o, &st, flags, d, MB2_UPPER[o.prob], o.cap ? o.cap : (1ull << 27)};
  ensure(f.n > 1 ? f.n : 1);
  for (int j = 0; j < d; j++) CK(cudaMemcpy(dA[j], f.c[j].data(), f.n * 4, cudaMemcpyHostToDevice));
  bfs(x, f.level, f.n);
  CK(cudaDeviceSynchronize());
  if (st.ok == 0) st.ok = st.unresolved == 0 && st.refuted == 0;
  return st;
}
