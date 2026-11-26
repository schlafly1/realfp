/* manybox GPU backend: the expressions of mbexpr.h with CUDA's per-instruction
   directed-rounding intrinsics, and the same level-synchronous bisection as mbcpu.c.
   Per level: eval kernel (one thread per box) -> CUB exclusive scan of the split flags ->
   scatter kernel writing the two children of every split box, in order. The only
   host<->device traffic per level is the 4-byte split count (and, if a certificate is
   requested, the flags). */
#include <cuda_runtime.h>
#include <cub/cub.cuh>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "mb.h"

#define IVQ static __device__ __forceinline__
#define ADD_D __dadd_rd
#define ADD_U __dadd_ru
#define SUB_D __dsub_rd
#define SUB_U __dsub_ru
#define MUL_D __dmul_rd
#define MUL_U __dmul_ru
#include "mbexpr.h"

#define TPB 256
#define CK(x) do { cudaError_t e_ = (x); if (e_ != cudaSuccess) { \
  fprintf(stderr, "CUDA error %s at %s:%d\n", cudaGetErrorString(e_), __FILE__, __LINE__); exit(2); } } while (0)

struct Coords { uint32_t *c[MB_MAXD]; };

template <int PROB>
__global__ void __launch_bounds__(TPB) k_eval(int level, uint64_t n, Coords A, double bound, uint32_t *fl) {
  const int d = PROB == 0 ? 2 : 4;
  uint64_t i = blockIdx.x * (uint64_t)blockDim.x + threadIdx.x;
  if (i >= n) return;
  mbiv X[MB_MAXD];
#pragma unroll
  for (int j = 0; j < d; j++) {
    double h = ldexp(2.0, -((level + d - 1 - j) / d));
    double c = (double)A.c[j][i];
    X[j].lo = __dadd_rn(-1.0, __dmul_rn(c, h));          /* exact */
    X[j].hi = __dadd_rn(-1.0, __dmul_rn(__dadd_rn(c, 1.0), h));
  }
  uint32_t f;
  if (PROB == 0) { mbiv F = mb_p1(X); f = !(F.hi <= bound); }
  else { mbiv F = mb_p2(X); f = !(F.lo >= bound); }
  fl[i] = f;
}

__global__ void __launch_bounds__(TPB) k_split(int d, int sd, uint64_t n, Coords A, Coords B,
                                               const uint32_t *fl, const uint32_t *off) {
  uint64_t i = blockIdx.x * (uint64_t)blockDim.x + threadIdx.x;
  if (i >= n || !fl[i]) return;
  uint64_t o = 2ull * off[i];
  for (int j = 0; j < d; j++) {
    uint32_t c = A.c[j][i];
    if (j == sd) { B.c[j][o] = 2 * c; B.c[j][o + 1] = 2 * c + 1; }
    else { B.c[j][o] = c; B.c[j][o + 1] = c; }
  }
}

__global__ void k_pack(uint64_t n, const uint32_t *fl, uint8_t *out) {
  uint64_t i = blockIdx.x * (uint64_t)blockDim.x + threadIdx.x;
  if (i < n) out[i] = (uint8_t)fl[i];
}

static uint32_t *dA[MB_MAXD], *dB[MB_MAXD], *dfl, *doff, *hcnt;
static uint8_t *dpk, *hpk;
static void *dtmp; static size_t tmpcap, cap;
static int inited;

static void ensure(int d, size_t need) {
  if (need <= cap) return;
  size_t nc = cap ? cap : 1 << 16; while (nc < need) nc *= 2;
  for (int j = 0; j < MB_MAXD; j++) {
    if (dA[j]) { CK(cudaFree(dA[j])); CK(cudaFree(dB[j])); }
    CK(cudaMalloc(&dA[j], nc * 4)); CK(cudaMalloc(&dB[j], nc * 4));
  }
  if (dfl) { CK(cudaFree(dfl)); CK(cudaFree(doff)); CK(cudaFree(dpk)); CK(cudaFreeHost(hpk)); }
  CK(cudaMalloc(&dfl, nc * 4)); CK(cudaMalloc(&doff, nc * 4)); CK(cudaMalloc(&dpk, nc));
  CK(cudaMallocHost(&hpk, nc));
  size_t t = 0; cub::DeviceScan::ExclusiveSum(NULL, t, dfl, doff, (int)nc);
  if (t > tmpcap) { if (dtmp) CK(cudaFree(dtmp)); CK(cudaMalloc(&dtmp, t)); tmpcap = t; }
  cap = nc; (void)d;
}

extern "C" int mb_gpu_init(char *name, int len) {
  if (!inited) {
    CK(cudaSetDevice(0)); CK(cudaFree(0));
    CK(cudaMallocHost(&hcnt, 16));
    ensure(4, 1 << 20);
    inited = 1;
  }
  cudaDeviceProp p; CK(cudaGetDeviceProperties(&p, 0));
  if (name) snprintf(name, len, "%s, %d SMs, cc %d.%d", p.name, p.multiProcessorCount, p.major, p.minor);
  return 0;
}

extern "C" mb_stats mb_gpu_run(int prob, double bound, int maxlevel, mb_cert *cert) {
  mb_gpu_init(NULL, 0);
  int d = MB_DIM[prob];
  mb_stats st = {0, 0, 0, 0, 0, 0, MB_FNV0};
  uint64_t n = 1;
  for (int j = 0; j < d; j++) CK(cudaMemsetAsync(dA[j], 0, 4));
  for (int level = 0; n > 0; level++) {
    st.levels = level + 1; st.evals += n; if (n > st.peak) st.peak = n;
    int last = level + 1 >= maxlevel;
    Coords A, B;
    for (int j = 0; j < MB_MAXD; j++) { A.c[j] = dA[j]; B.c[j] = dB[j]; }
    unsigned nb = (unsigned)((n + TPB - 1) / TPB);
    if (prob == 0) k_eval<0><<<nb, TPB>>>(level, n, A, bound, dfl);
    else k_eval<1><<<nb, TPB>>>(level, n, A, bound, dfl);
    size_t t = tmpcap;
    CK(cub::DeviceScan::ExclusiveSum(dtmp, t, dfl, doff, (int)n));
    CK(cudaMemcpyAsync(hcnt, doff + (n - 1), 4, cudaMemcpyDeviceToHost));
    CK(cudaMemcpyAsync(hcnt + 1, dfl + (n - 1), 4, cudaMemcpyDeviceToHost));
    if (cert) {
      k_pack<<<nb, TPB>>>(n, dfl, dpk);
      CK(cudaMemcpyAsync(hpk, dpk, n, cudaMemcpyDeviceToHost));
    }
    CK(cudaStreamSynchronize(0));
    uint64_t nf = (uint64_t)hcnt[0] + hcnt[1];
    if (cert) {
      if (cert->len + n > cert->cap) {
        while (cert->len + n > cert->cap) cert->cap = cert->cap ? 2 * cert->cap : 1 << 20;
        cert->flags = (uint8_t *)realloc(cert->flags, cert->cap);
      }
      memcpy(cert->flags + cert->len, hpk, n); cert->len += n;
      st.hash = mb_fnv(st.hash, hpk, n);
    }
    st.leaves += n - nf;
    if (nf == 0) { st.ok = 1; break; }
    if (last) { st.unresolved = nf; break; }
    if (2 * nf > cap) {
      /* grow, keeping the current level's coordinates, flags and offsets */
      size_t oc = cap;
      uint32_t *keepA[MB_MAXD], *kfl, *koff;
      for (int j = 0; j < MB_MAXD; j++) { CK(cudaMalloc(&keepA[j], oc * 4)); CK(cudaMemcpy(keepA[j], dA[j], n * 4, cudaMemcpyDeviceToDevice)); }
      CK(cudaMalloc(&kfl, oc * 4)); CK(cudaMalloc(&koff, oc * 4));
      CK(cudaMemcpy(kfl, dfl, n * 4, cudaMemcpyDeviceToDevice)); CK(cudaMemcpy(koff, doff, n * 4, cudaMemcpyDeviceToDevice));
      ensure(d, 2 * nf);
      for (int j = 0; j < MB_MAXD; j++) { CK(cudaMemcpy(dA[j], keepA[j], n * 4, cudaMemcpyDeviceToDevice)); CK(cudaFree(keepA[j])); }
      CK(cudaMemcpy(dfl, kfl, n * 4, cudaMemcpyDeviceToDevice)); CK(cudaMemcpy(doff, koff, n * 4, cudaMemcpyDeviceToDevice));
      CK(cudaFree(kfl)); CK(cudaFree(koff));
      for (int j = 0; j < MB_MAXD; j++) { A.c[j] = dA[j]; B.c[j] = dB[j]; }
    }
    k_split<<<nb, TPB>>>(d, level % d, n, A, B, dfl, doff);
    CK(cudaGetLastError());
    for (int j = 0; j < MB_MAXD; j++) { uint32_t *tt = dA[j]; dA[j] = dB[j]; dB[j] = tt; }
    n = 2 * nf;
  }
  CK(cudaDeviceSynchronize());
  return st;
}
