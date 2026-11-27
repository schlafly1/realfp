/* realfp-grid GPU engine (CUDA): level-synchronous bisection, one thread per box, the tape in
   constant memory. fp64 uses CUDA's per-instruction directed rounding (__dadd_rd ...: the same
   results as the checker); fp32 (__fadd_rd ...) gives sound, slightly wider enclosures and is
   faster on GPUs with few fp64 units. Box endpoints and split points are always binary64.
   Build with -fmad=false (no contraction) -prec-div=true -prec-sqrt=true. */
#include <cuda_runtime.h>
#include <cub/cub.cuh>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <string>
#include "ops.hpp"
#include "grid.hpp"

#define RFG_GPU_MAXT 256
#define TPB 128
#define CK(x) do { cudaError_t e_ = (x); if (e_ != cudaSuccess) { \
  fprintf(stderr, "realfp-grid: CUDA error %s at %s:%d\n", cudaGetErrorString(e_), __FILE__, __LINE__); exit(3); } } while (0)

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

__constant__ uint32_t c_code[3 * RFG_GPU_MAXT];
__constant__ double c_k[2 * RFG_GPU_MAXT];

struct Par { uint32_t d, n; int upper; double c; float c32; };

template <class R>
__device__ __forceinline__ IVT<typename R::T> eval_box(const Par &p, const double *box, uint64_t stride,
                                                        uint64_t i, bool point) {
  typedef typename R::T T;
  IVT<T> X[RFG_MAXD], K[1];
  (void)K;
  IVT<T> Reg[RFG_GPU_MAXT];
  for (uint32_t j = 0; j < p.d; j++) {
    double lo = box[(2 * j) * stride + i], hi = box[(2 * j + 1) * stride + i];
    if (point) { double m = midF(lo, hi); lo = m; hi = m; }
    X[j].lo = R::lo_of(lo); X[j].hi = R::hi_of(hi);
  }
  /* constants: converted per use (lo rounded down, hi up) */
  for (uint32_t k = 0; k < p.n; k++) {
    uint32_t op = c_code[3 * k], a = c_code[3 * k + 1], b = c_code[3 * k + 2];
    switch (op) {
      case 0: { IVT<T> z = {(T)0, (T)0}; Reg[k] = a < p.d ? X[a] : z; break; }
      case 1: Reg[k].lo = R::lo_of(c_k[2 * a]); Reg[k].hi = R::hi_of(c_k[2 * a + 1]); break;
      case 2: Reg[k] = iv_add<R>(Reg[a], Reg[b]); break;
      case 3: Reg[k] = iv_sub<R>(Reg[a], Reg[b]); break;
      case 4: Reg[k] = iv_mul<R>(Reg[a], Reg[b]); break;
      case 5: Reg[k] = iv_neg(Reg[a]); break;
      case 6: Reg[k] = iv_pown<R>(Reg[a], b); break;
      case 7: Reg[k] = iv_mul<R>(Reg[a], iv_inv<R>(Reg[b])); break;
      case 8: Reg[k] = iv_sqrtI<R>(Reg[a]); break;
      default: Reg[k] = iv_invalid<R>(); break;
    }
  }
  return Reg[p.n - 1];
}

template <class R>
__global__ void __launch_bounds__(TPB) k_eval(Par p, uint64_t n, const double *box, int L, int maxLevel,
                                              uint32_t *fl, uint8_t *flb, unsigned long long *failAt) {
  uint64_t i = blockIdx.x * (uint64_t)blockDim.x + threadIdx.x;
  if (i >= n) return;
  typedef typename R::T T;
  IVT<T> F = eval_box<R>(p, box, n, i, false);
  bool ok;
  if (isn_(F.lo) || isn_(F.hi)) ok = false;
  else if (sizeof(T) == 4) ok = p.upper ? ((float)F.hi <= p.c32) : (p.c32 <= (float)F.lo);
  else ok = p.upper ? ((double)F.hi <= p.c) : (p.c <= (double)F.lo);
  if (ok) { fl[i] = 0; flb[i] = 0; return; }
  uint32_t vi = L % p.d;
  double m = midF(box[(2 * vi) * n + i], box[(2 * vi + 1) * n + i]);
  if (L >= maxLevel || isn_(m)) atomicMin(failAt, (unsigned long long)i);
  fl[i] = 1; flb[i] = 1;
}

__global__ void k_children(uint32_t d, uint64_t n, uint64_t n2, const double *cur, double *nxt,
                           const uint32_t *fl, const uint32_t *off, uint32_t vi) {
  uint64_t i = blockIdx.x * (uint64_t)blockDim.x + threadIdx.x;
  if (i >= n || !fl[i]) return;
  uint64_t o = 2 * off[i];
  for (uint32_t j = 0; j < 2 * d; j++) { double v = cur[j * n + i]; nxt[j * n2 + o] = v; nxt[j * n2 + o + 1] = v; }
  double m = midF(cur[(2 * vi) * n + i], cur[(2 * vi + 1) * n + i]);
  nxt[(2 * vi + 1) * n2 + o] = m;
  nxt[(2 * vi) * n2 + o + 1] = m;
}

template <class R>
__global__ void k_mm(Par p, uint64_t n, const double *box, double *out) {
  uint64_t i = blockIdx.x * (uint64_t)blockDim.x + threadIdx.x;
  if (i >= n) return;
  IVT<typename R::T> F = eval_box<R>(p, box, n, i, false);
  IVT<typename R::T> G = eval_box<R>(p, box, n, i, true);
  out[i] = (double)F.lo; out[n + i] = (double)F.hi; out[2 * n + i] = (double)G.lo; out[3 * n + i] = (double)G.hi;
}

static float f32_down(double c) { float f = (float)c; if ((double)f > c) f = nextafterf(f, -INFINITY); return f; }
static float f32_up(double c) { float f = (float)c; if ((double)f < c) f = nextafterf(f, INFINITY); return f; }

struct GpuEngine : Engine {
  Problem P; Opts o; bool fp32; Par par;
  double *dcur = nullptr, *dnxt = nullptr; uint32_t *dfl = nullptr; uint32_t *doff = nullptr;
  uint8_t *dflb = nullptr; unsigned long long *dfail = nullptr; void *dtmp = nullptr; size_t tmpBytes = 0;
  uint64_t capBuf = 0;
  GpuEngine(const Problem &p, const Opts &op, bool f32) : P(p), o(op), fp32(f32) {
    CK(cudaMemcpyToSymbol(c_code, P.code.data(), P.code.size() * 4));
    if (!P.k.empty()) CK(cudaMemcpyToSymbol(c_k, P.k.data(), P.k.size() * 8));
    par.d = P.d; par.n = P.n(); par.upper = P.upper; par.c = P.c;
    par.c32 = P.upper ? f32_down(P.c) : f32_up(P.c);
    CK(cudaMalloc(&dfail, sizeof(unsigned long long)));
  }
  ~GpuEngine() { cudaFree(dcur); cudaFree(dnxt); cudaFree(dfl); cudaFree(doff); cudaFree(dflb); cudaFree(dfail); cudaFree(dtmp); }
  const char *name() const override { return fp32 ? "gpu-fp32" : "gpu-fp64"; }

  uint64_t default_cap() {
    size_t fr = 0, tot = 0; CK(cudaMemGetInfo(&fr, &tot));
    uint64_t per = 32ull * P.d + 4 + 4 + 1;
    uint64_t c = (uint64_t)(0.5 * (double)fr) / per;
    if (c > (1ull << 28)) c = 1ull << 28;
    return c;
  }
  void ensure(uint64_t cap) {
    if (cap <= capBuf) return;
    cudaFree(dcur); cudaFree(dnxt); cudaFree(dfl); cudaFree(doff); cudaFree(dflb); cudaFree(dtmp);
    CK(cudaMalloc(&dcur, cap * 2 * P.d * 8)); CK(cudaMalloc(&dnxt, cap * 2 * P.d * 8));
    CK(cudaMalloc(&dfl, cap * 4)); CK(cudaMalloc(&doff, cap * 4)); CK(cudaMalloc(&dflb, cap));
    tmpBytes = 0;
    CK(cub::DeviceScan::ExclusiveSum(nullptr, tmpBytes, dfl, doff, (int64_t)cap));
    CK(cudaMalloc(&dtmp, tmpBytes));
    capBuf = cap;
  }

  RunStatus run(const double *box0, int l0, int maxLevel, uint64_t cap,
                std::vector<std::vector<uint8_t>> &flags, Stats &st, FailInfo &fi) override {
    if (cap == 0) cap = default_cap();
    ensure(cap);
    const uint32_t d = P.d;
    CK(cudaMemcpy(dcur, box0, 2 * d * 8, cudaMemcpyHostToDevice));   /* n = 1: stride 1 */
    uint64_t n = 1;
    flags.clear();
    for (int L = l0;; L++) {
      unsigned long long none = ~0ull;
      CK(cudaMemcpy(dfail, &none, 8, cudaMemcpyHostToDevice));
      uint64_t blocks = (n + TPB - 1) / TPB;
      if (fp32) k_eval<G32><<<blocks, TPB>>>(par, n, dcur, L, maxLevel, dfl, dflb, dfail);
      else k_eval<G64><<<blocks, TPB>>>(par, n, dcur, L, maxLevel, dfl, dflb, dfail);
      CK(cudaGetLastError());
      size_t tb = tmpBytes;
      CK(cub::DeviceScan::ExclusiveSum(dtmp, tb, dfl, doff, (int64_t)n));
      std::vector<uint8_t> fl(n);
      CK(cudaMemcpy(fl.data(), dflb, n, cudaMemcpyDeviceToHost));
      unsigned long long fa; CK(cudaMemcpy(&fa, dfail, 8, cudaMemcpyDeviceToHost));
      uint32_t lastOff; CK(cudaMemcpy(&lastOff, doff + n - 1, 4, cudaMemcpyDeviceToHost));
      uint64_t splits = lastOff + fl[n - 1];
      st.boxes += n;
      if (L > st.maxLevel) st.maxLevel = L;
      if (fa != ~0ull) {
        std::vector<double> b(2 * d * n);
        CK(cudaMemcpy(b.data(), dcur, 2 * d * n * 8, cudaMemcpyDeviceToHost));
        fi.level = L;
        for (uint32_t j = 0; j < 2 * d; j++) fi.box[j] = b[j * n + fa];
        Engine *c = make_cpu(P, o);    /* exact fp64 enclosure of the failing box */
        double flo, fhi, plo, phi; c->eval_mm(fi.box, 1, &flo, &fhi, &plo, &phi); delete c;
        fi.flo = flo; fi.fhi = fhi;
        return RUN_FAIL;
      }
      st.leaves += n - splits;
      flags.push_back(std::move(fl));
      if (splits == 0) return RUN_OK;
      if (o.maxBoxes && st.boxes + 2 * splits > o.maxBoxes) { fi.level = -1; return RUN_FAIL; }
      if (2 * splits > cap) return RUN_OVERFLOW;
      uint64_t n2 = 2 * splits;
      k_children<<<blocks, TPB>>>(d, n, n2, dcur, dnxt, dfl, doff, L % d);
      CK(cudaGetLastError());
      std::swap(dcur, dnxt); n = n2;
    }
  }

  void eval_mm(const double *box, uint64_t n, double *flo, double *fhi, double *plo,
               double *phi) override {
    double *db, *dout;
    CK(cudaMalloc(&db, n * 2 * P.d * 8)); CK(cudaMalloc(&dout, n * 4 * 8));
    CK(cudaMemcpy(db, box, n * 2 * P.d * 8, cudaMemcpyHostToDevice));
    uint64_t blocks = (n + TPB - 1) / TPB;
    if (fp32) k_mm<G32><<<blocks, TPB>>>(par, n, db, dout); else k_mm<G64><<<blocks, TPB>>>(par, n, db, dout);
    CK(cudaGetLastError());
    std::vector<double> out(4 * n);
    CK(cudaMemcpy(out.data(), dout, n * 4 * 8, cudaMemcpyDeviceToHost));
    memcpy(flo, out.data(), n * 8); memcpy(fhi, out.data() + n, n * 8);
    memcpy(plo, out.data() + 2 * n, n * 8); memcpy(phi, out.data() + 3 * n, n * 8);
    cudaFree(db); cudaFree(dout);
  }
};

bool gpu_available(std::string &desc) {
  int nd = 0;
  if (cudaGetDeviceCount(&nd) != cudaSuccess || nd == 0) { desc = "no CUDA device"; return false; }
  cudaDeviceProp pr; CK(cudaGetDeviceProperties(&pr, 0));
  desc = std::string(pr.name) + " (" + std::to_string(pr.multiProcessorCount) + " SMs, cc " +
         std::to_string(pr.major) + "." + std::to_string(pr.minor) + ")";
  return true;
}

Engine *make_gpu(const Problem &P, const Opts &o, bool fp32) {
  std::string d;
  if (!gpu_available(d)) return nullptr;
  if (P.n() > RFG_GPU_MAXT || P.k.size() / 2 > RFG_GPU_MAXT) return nullptr;
  return new GpuEngine(P, o, fp32);
}
