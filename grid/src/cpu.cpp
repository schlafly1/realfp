/* realfp-grid CPU engine: fp64 with realfp's portable directed-rounding kernels (round to
   nearest + exact error term, c/iv64_rnerr.h: exactly the results of the checker), std::thread. */
#include <math.h>
#include <string.h>
#include <thread>
#include <atomic>
#include <algorithm>
#include "../../c/iv64_rnerr.h"
#include "ops.hpp"
#include "grid.hpp"

struct C64 {
  typedef double T;
  static inline double add_d(double a, double b) { return iv64r_add(a, b, 0); }
  static inline double add_u(double a, double b) { return iv64r_add(a, b, 1); }
  static inline double sub_d(double a, double b) { return iv64r_sub(a, b, 0); }
  static inline double sub_u(double a, double b) { return iv64r_sub(a, b, 1); }
  static inline double mul_d(double a, double b) { return iv64r_mul(a, b, 0); }
  static inline double mul_u(double a, double b) { return iv64r_mul(a, b, 1); }
  static inline double div_d(double a, double b) { return iv64r_div(a, b, 0); }
  static inline double div_u(double a, double b) { return iv64r_div(a, b, 1); }
  static inline double sqrt_d(double a) { return iv64r_sqrt(a, 0); }
  static inline double sqrt_u(double a) { return iv64r_sqrt(a, 1); }
  static inline double inf() { return INFINITY; }
  static inline double nan() { return NAN; }
};

template <class F> static void par_for(int T, uint64_t n, F f) {
  if (T <= 1 || n < 4096) { f(0, 0, n); return; }
  std::vector<std::thread> th;
  uint64_t chunk = (n + T - 1) / T;
  for (int t = 0; t < T; t++) {
    uint64_t a = t * chunk, b = std::min(n, a + chunk);
    if (a >= b) break;
    th.emplace_back([=]() { f(t, a, b); });
  }
  for (auto &x : th) x.join();
}

struct CpuEngine : Engine {
  Problem P; Opts o; int T;
  std::vector<IVT<double>> K;
  CpuEngine(const Problem &p, const Opts &op) : P(p), o(op) {
    T = o.threads > 0 ? o.threads : (int)std::max(1u, std::thread::hardware_concurrency());
    for (size_t j = 0; j + 1 < P.k.size(); j += 2) K.push_back({P.k[j], P.k[j + 1]});
  }
  const char *name() const override { return "cpu-fp64"; }

  inline IVT<double> eval1(const double *box, uint64_t stride, uint64_t i, IVT<double> *R) const {
    IVT<double> X[RFG_MAXD];
    for (uint32_t j = 0; j < P.d; j++) { X[j].lo = box[(2 * j) * stride + i]; X[j].hi = box[(2 * j + 1) * stride + i]; }
    return tape_eval<C64>(P.code.data(), P.n(), K.data(), X, P.d, R);
  }
  inline bool ok(IVT<double> F) const {
    if (isn_(F.lo) || isn_(F.hi)) return false;
    return P.upper ? F.hi <= P.c : P.c <= F.lo;
  }

  uint64_t default_cap() override { return 1ull << 23; }

  RunStatus run(const double *roots, uint64_t R, int l0, int maxLevel, uint64_t cap,
                std::vector<std::vector<uint8_t>> &flags, std::vector<double> &holes, Stats &st,
                FailInfo &fi) override {
    const uint32_t d = P.d;
    std::vector<double> cur(2 * d * R), nxt;
    for (uint64_t r = 0; r < R; r++)
      for (uint32_t j = 0; j < 2 * d; j++) cur[j * R + r] = roots[2 * d * r + j];
    uint64_t n = R;
    flags.clear();
    for (int L = l0;; L++) {
      std::vector<uint8_t> fl(n);
      std::vector<uint64_t> cnt(T + 1, 0);
      std::atomic<uint64_t> failAt(~0ull);
      const uint32_t vi = L % d;
      par_for(T, n, [&](int t, uint64_t a, uint64_t b) {
        std::vector<IVT<double>> R(P.n());
        uint64_t c = 0;
        for (uint64_t i = a; i < b; i++) {
          IVT<double> F = eval1(cur.data(), n, i, R.data());
          if (ok(F)) { fl[i] = 0; continue; }
          double m = midF(cur[(2 * vi) * n + i], cur[(2 * vi + 1) * n + i]);
          if (L >= maxLevel || isn_(m)) {
            fl[i] = 2;
            uint64_t e = failAt.load();
            while (i < e && !failAt.compare_exchange_weak(e, i)) {}
            continue;
          }
          fl[i] = 1; c++;
        }
        cnt[t + 1] = c;
      });
      st.boxes += n;
      if (L > st.maxLevel) st.maxLevel = L;
      if (failAt.load() != ~0ull) {
        uint64_t i = failAt.load();
        std::vector<IVT<double>> R(P.n());
        IVT<double> F = eval1(cur.data(), n, i, R.data());
        fi.level = L; fi.flo = F.lo; fi.fhi = F.hi;
        for (uint32_t j = 0; j < 2 * d; j++) fi.box[j] = cur[j * n + i];
        return RUN_FAIL;
      }
      uint64_t splits = 0;
      for (int t = 0; t < T; t++) { cnt[t + 1] += cnt[t]; }
      splits = cnt[T];
      st.leaves += n - splits;
      flags.push_back(std::move(fl));
      if (splits == 0) return RUN_OK;
      if (o.maxBoxes && st.boxes + 2 * splits > o.maxBoxes) { fi.level = -1; return RUN_FAIL; }
      if (2 * splits > cap) {
        holes.assign(2 * d * splits, 0.0);
        const std::vector<uint8_t> &F = flags.back();
        uint64_t h = 0;
        for (uint64_t i = 0; i < n; i++)
          if (F[i] == 1) { for (uint32_t j = 0; j < 2 * d; j++) holes[2 * d * h + j] = cur[j * n + i]; h++; }
        return RUN_OVERFLOW;
      }
      uint64_t n2 = 2 * splits;
      nxt.assign(2 * d * n2, 0.0);
      const std::vector<uint8_t> &F = flags.back();
      par_for(T, n, [&](int t, uint64_t a, uint64_t b) {
        uint64_t o2 = 2 * cnt[t];
        for (uint64_t i = a; i < b; i++) {
          if (F[i] != 1) continue;
          for (uint32_t j = 0; j < 2 * d; j++) { double v = cur[j * n + i]; nxt[j * n2 + o2] = v; nxt[j * n2 + o2 + 1] = v; }
          double m = midF(cur[(2 * vi) * n + i], cur[(2 * vi + 1) * n + i]);
          nxt[(2 * vi + 1) * n2 + o2] = m;      /* left: hi = m */
          nxt[(2 * vi) * n2 + o2 + 1] = m;      /* right: lo = m */
          o2 += 2;
        }
      });
      cur.swap(nxt); n = n2;
    }
  }

  void eval_mm(const double *box, uint64_t n, double *flo, double *fhi, double *plo,
               double *phi) override {
    par_for(T, n, [&](int, uint64_t a, uint64_t b) {
      std::vector<IVT<double>> R(P.n());
      std::vector<double> pt(2 * P.d);
      for (uint64_t i = a; i < b; i++) {
        IVT<double> F = eval1(box, n, i, R.data());
        flo[i] = F.lo; fhi[i] = F.hi;
        IVT<double> X[RFG_MAXD];
        for (uint32_t j = 0; j < P.d; j++) {
          double m = midF(box[(2 * j) * n + i], box[(2 * j + 1) * n + i]);
          X[j].lo = m; X[j].hi = m;
        }
        IVT<double> G = tape_eval<C64>(P.code.data(), P.n(), K.data(), X, P.d, R.data());
        plo[i] = G.lo; phi[i] = G.hi;
      }
    });
  }
};

Engine *make_cpu(const Problem &P, const Opts &o) { return new CpuEngine(P, o); }
