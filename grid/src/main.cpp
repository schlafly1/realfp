/* realfp-grid: search tool for realfp's many-box certificates (docs/GPU.md).

   realfp-grid info
   realfp-grid prove  PROBLEM -o CERT [--engine auto|cpu|gpu|gpu32|gpu64] [--depth N]
                      [--max-boxes N] [--cap N] [--threads N] [--split K] [-v]
   realfp-grid minmax PROBLEM [--max] [--engine ...] [--depth N] [--cap N] [--tol X] [--time S]

   PROBLEM files are written by the `interval_grid` tactic (RealFPGrid/Tactic.lean). Nothing this
   tool computes is trusted: certificates are checked by Lean. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <chrono>
#include <string>
#include <vector>
#include <algorithm>
#include "grid.hpp"

static double now() {
  return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count();
}

struct BitW {
  std::string hex; unsigned cur = 0, n = 0; uint64_t bits = 0;
  void put(int b) {
    cur = 2 * cur + (b ? 1 : 0); n++; bits++;
    if (n == 4) { hex.push_back("0123456789abcdef"[cur]); cur = 0; n = 0; }
  }
  std::string done() { std::string h = hex; if (n) h.push_back("0123456789abcdef"[cur << (4 - n)]); return h; }
};

static void emit_preorder(const std::vector<std::vector<uint8_t>> &fl, BitW &w) {
  std::vector<size_t> idx(fl.size() + 1, 0);
  std::vector<int> stk; stk.push_back(0);
  while (!stk.empty()) {
    int l = stk.back(); stk.pop_back();
    uint8_t f = fl[l][idx[l]++];
    if (f == 0) w.put(0);
    else { w.put(1); stk.push_back(l + 1); stk.push_back(l + 1); }
  }
}

struct Ctx {
  const Problem *P; Engine *E; Opts o; int maxLevel; Stats st; FailInfo fi; int runs = 0, overflows = 0;
};

static void children(const Problem &P, const double *box, int l, double *L, double *R, double &m) {
  uint32_t i = l % P.d;
  memcpy(L, box, 2 * P.d * 8); memcpy(R, box, 2 * P.d * 8);
  m = (box[2 * i] * 0.5) + (box[2 * i + 1] * 0.5);
  { volatile double a = box[2 * i] * 0.5, b = box[2 * i + 1] * 0.5; m = a + b; }
  L[2 * i + 1] = m; R[2 * i] = m;
}

/* box: AoS (lo0, hi0, lo1, hi1, ...) here; engines take one root box (stride 1 = same layout). */
static RunStatus solve(Ctx &C, const double *box, int l, BitW &w) {
  std::vector<std::vector<uint8_t>> fl;
  C.runs++;
  RunStatus r = C.E->run(box, l, C.maxLevel, C.o.cap, fl, C.st, C.fi);
  if (r == RUN_OK) { emit_preorder(fl, w); return RUN_OK; }
  if (r == RUN_FAIL) return r;
  C.overflows++;
  double Lb[2 * RFG_MAXD], Rb[2 * RFG_MAXD], m;
  children(*C.P, box, l, Lb, Rb, m);
  w.put(1);
  RunStatus a = solve(C, Lb, l + 1, w);
  if (a != RUN_OK) return a;
  return solve(C, Rb, l + 1, w);
}

struct Job { int l0; std::string hex; };

/* Bit reader over a hex certificate (missing bits = 0, as in the checker). */
struct BitR {
  const std::string &h; explicit BitR(const std::string &s) : h(s) {}
  inline int at(uint64_t i) const {
    uint64_t j = i / 4; if (j >= h.size()) return 0;
    char c = h[j]; int v = (c >= '0' && c <= '9') ? c - '0' : (c >= 'a' && c <= 'f') ? c - 'a' + 10 : 0;
    return (v >> (3 - i % 4)) & 1;
  }
};
static uint64_t skip_tree(const BitR &r, uint64_t pos) {
  uint64_t pending = 1;
  while (pending) { pending--; if (r.at(pos++)) pending += 2; }
  return pos;
}
/* Split a certificate at depth K: the top tree (1 = split, 0 = sub-check) and the sub-checks
   (`Top.sub l0 hex`: the subtree rooted at depth l0 <= K; a leaf above K is a sub-check "0"). */
static void split_cert(const std::string &hex, int K, BitW &top, std::vector<Job> &jobs) {
  BitR r(hex);
  struct Fr { int l; };
  std::vector<int> stk; stk.push_back(0);
  uint64_t pos = 0;
  while (!stk.empty()) {
    int l = stk.back(); stk.pop_back();
    if (l == K || !r.at(pos)) {
      uint64_t q = (l == K) ? skip_tree(r, pos) : pos + 1;
      BitW w; for (uint64_t i = pos; i < q; i++) w.put(r.at(i));
      jobs.push_back({l, w.done()}); top.put(0); pos = q;
    } else { top.put(1); pos++; stk.push_back(l + 1); stk.push_back(l + 1); }
  }
}

static bool read_cert_line(const char *path, std::string &line) {
  FILE *f = fopen(path, "rb"); if (!f) return false;
  std::string cur; int ch;
  line.clear();
  while ((ch = fgetc(f)) != EOF) {
    if (ch == '\n') { if (!cur.empty() && cur[0] != '#') { line = cur; break; } cur.clear(); }
    else cur.push_back((char)ch);
  }
  if (line.empty() && !cur.empty() && cur[0] != '#') line = cur;
  fclose(f); return !line.empty();
}

static bool write_split(const char *out, const Problem &P, const std::string &info, BitW &top,
                        std::vector<Job> &jobs) {
  FILE *f = fopen(out, "wb");
  if (!f) return false;
  fprintf(f, "# realfp-grid split certificate v1\n# problem fnv %016llx\n# %s\n", (unsigned long long)P.fnv, info.c_str());
  fprintf(f, "top %s\n", top.done().c_str());
  for (auto &j : jobs) fprintf(f, "job %d %s\n", j.l0, j.hex.c_str());
  fclose(f);
  return true;
}

static void usage() {
  fprintf(stderr,
    "usage: realfp-grid info\n"
    "       realfp-grid prove PROBLEM -o CERT [--engine auto|cpu|gpu|gpu32|gpu64] [--depth N]\n"
    "                         [--max-boxes N] [--cap N] [--threads N] [--split K] [-v]\n"
    "       realfp-grid split PROBLEM CERT K -o SPLITCERT\n"
    "       realfp-grid minmax PROBLEM [--max] [--engine E] [--depth N] [--cap N] [--tol X] [--time S]\n");
  exit(2);
}

static Engine *pick(const std::string &eng, const Problem &P, const Opts &o) {
  Engine *E = nullptr;
  if (eng == "gpu" || eng == "gpu32" || eng == "auto") E = make_gpu(P, o, true);
  else if (eng == "gpu64") E = make_gpu(P, o, false);
  if (!E && eng != "auto" && eng != "cpu") { fprintf(stderr, "realfp-grid: no usable GPU (engine %s)\n", eng.c_str()); exit(4); }
  if (!E) E = make_cpu(P, o);
  return E;
}

static void print_box(const Problem &P, const double *b) {
  for (uint32_t j = 0; j < P.d; j++) printf("%s[%.17g, %.17g]", j ? " x " : "", b[2 * j], b[2 * j + 1]);
}

int main(int argc, char **argv) {
  if (argc < 2) usage();
  std::string mode = argv[1];
  if (mode == "info") {
    std::string d; bool g = gpu_available(d);
    printf("realfp-grid 1\nengines: cpu-fp64%s\ngpu: %s\n", g ? ", gpu-fp32, gpu-fp64" : "", d.c_str());
    return 0;
  }
  if (mode == "split") {
    if (argc != 7 || strcmp(argv[5], "-o") != 0) usage();
    Problem P; std::string err;
    if (!read_problem(argv[2], P, err)) { fprintf(stderr, "realfp-grid: %s\n", err.c_str()); return 2; }
    std::string hex;
    if (!read_cert_line(argv[3], hex)) { fprintf(stderr, "realfp-grid: cannot read %s\n", argv[3]); return 2; }
    int K = atoi(argv[4]);
    double t0 = now();
    BitW top; std::vector<Job> jobs;
    split_cert(hex, K, top, jobs);
    if (!write_split(argv[6], P, std::string("split of ") + argv[3], top, jobs)) { fprintf(stderr, "realfp-grid: cannot write %s\n", argv[6]); return 2; }
    printf("OK: %zu sub-checks (depth %d), %.3f s -> %s\n", jobs.size(), K, now() - t0, argv[6]);
    return 0;
  }
  if (argc < 3) usage();
  const char *pf = argv[2], *out = nullptr;
  Opts o; std::string eng = "auto"; int K = -1; bool mx = false; double tol = 0, tmax = 0;
  for (int i = 3; i < argc; i++) {
    std::string a = argv[i];
    auto val = [&]() -> const char * { if (i + 1 >= argc) usage(); return argv[++i]; };
    if (a == "-o") out = val();
    else if (a == "--engine") eng = val();
    else if (a == "--depth") o.maxDepth = atoi(val());
    else if (a == "--max-boxes") o.maxBoxes = strtoull(val(), nullptr, 10);
    else if (a == "--cap") o.cap = strtoull(val(), nullptr, 10);
    else if (a == "--threads") o.threads = atoi(val());
    else if (a == "--split") K = atoi(val());
    else if (a == "--max") mx = true;
    else if (a == "--tol") tol = atof(val());
    else if (a == "--time") tmax = atof(val());
    else if (a == "-v") o.verbose = true;
    else usage();
  }
  Problem P; std::string err;
  if (!read_problem(pf, P, err)) { fprintf(stderr, "realfp-grid: %s\n", err.c_str()); return 2; }
  if (o.maxDepth <= 0) o.maxDepth = std::min(1000, 30 * (int)P.d);
  if (o.cap == 0 && eng == "cpu") o.cap = 1ull << 24;
  Engine *E = pick(eng, P, o);
  double box[2 * RFG_MAXD];
  for (uint32_t j = 0; j < P.d; j++) { box[2 * j] = P.lo[j]; box[2 * j + 1] = P.hi[j]; }

  if (mode == "prove") {
    if (!out) usage();
    if (o.cap == 0 && strncmp(E->name(), "cpu", 3) == 0) o.cap = 1ull << 24;
    Ctx C; C.P = &P; C.E = E; C.o = o; C.maxLevel = o.maxDepth;
    double t0 = now();
    BitW w; RunStatus r = solve(C, box, 0, w);
    double t1 = now();
    if (r != RUN_OK) {
      if (C.fi.level < 0) printf("FAIL: box budget %llu exhausted after %.3f s\n", (unsigned long long)o.maxBoxes, t1 - t0);
      else {
        printf("FAIL: no certificate within depth %d (%s, %.3f s, %llu boxes).\n  box at level %d: ", o.maxDepth, E->name(),
               t1 - t0, (unsigned long long)C.st.boxes, C.fi.level);
        print_box(P, C.fi.box);
        printf("\n  fp64 enclosure of f there: [%.17g, %.17g], bound %s %.17g\n", C.fi.flo, C.fi.fhi, P.upper ? "<=" : ">=", P.c);
        bool refuted = P.upper ? C.fi.flo > P.c : C.fi.fhi < P.c;
        if (refuted) printf("  REFUTED: the bound is false on this whole box.\n");
      }
      return 1;
    }
    char info[512];
    snprintf(info, sizeof info, "engine %s, %llu boxes, %llu leaves, max level %d, %d runs, %.3f s", E->name(),
             (unsigned long long)C.st.boxes, (unsigned long long)C.st.leaves, C.st.maxLevel, C.runs, t1 - t0);
    std::string hex = w.done();
    if (K >= 0) {
      BitW top; std::vector<Job> jobs;
      split_cert(hex, K, top, jobs);
      if (!write_split(out, P, info, top, jobs)) { fprintf(stderr, "realfp-grid: cannot write %s\n", out); return 2; }
      printf("OK: %s, %zu sub-checks (split at depth %d) -> %s\n", info, jobs.size(), K, out);
      return 0;
    }
    FILE *f = fopen(out, "wb");
    if (!f) { fprintf(stderr, "realfp-grid: cannot write %s\n", out); return 2; }
    fprintf(f, "# realfp-grid certificate v1\n# problem fnv %016llx\n# %s\n%s\n", (unsigned long long)P.fnv, info, hex.c_str());
    fclose(f);
    printf("OK: %s -> %s\n", info, out);
    return 0;
  }

  if (mode == "minmax") {
    /* branch and bound for min f (or max f with --max) over the box; rigorous enclosure [L, U]
       of the extremum: U from point evaluations (midpoints), L from box enclosures. */
    const uint32_t d = P.d;
    uint64_t cap = o.cap ? o.cap : (1ull << 22);
    double t0 = now();
    std::vector<double> cur(2 * d); for (uint32_t j = 0; j < 2 * d; j++) cur[j] = box[(j % 2) ? 2 * (j / 2) + 1 : 2 * (j / 2)];
    for (uint32_t j = 0; j < d; j++) { cur[2 * j] = box[2 * j]; cur[2 * j + 1] = box[2 * j + 1]; }
    /* SoA with n = 1 equals AoS */
    uint64_t n = 1; double U = INFINITY, dropped = INFINITY; std::vector<double> arg(d);
    uint64_t evals = 0; int L = 0; double Lb = -INFINITY;
    for (L = 0; L <= o.maxDepth; L++) {
      std::vector<double> flo(n), fhi(n), plo(n), phi(n);
      E->eval_mm(cur.data(), n, flo.data(), fhi.data(), plo.data(), phi.data());
      evals += n;
      /* work with g = f (min) or g = -f (max) */
      std::vector<double> glo(n);
      for (uint64_t i = 0; i < n; i++) {
        double lo = mx ? -fhi[i] : flo[i], pu = mx ? -plo[i] : phi[i];
        glo[i] = (lo != lo) ? -INFINITY : lo;
        if (pu == pu && pu < U) {
          U = pu;
          for (uint32_t j = 0; j < d; j++) arg[j] = 0.5 * cur[(2 * j) * n + i] + 0.5 * cur[(2 * j + 1) * n + i];
        }
      }
      double mn = dropped;
      std::vector<uint64_t> keep;
      for (uint64_t i = 0; i < n; i++) { if (glo[i] <= U) { keep.push_back(i); mn = std::min(mn, glo[i]); } }
      Lb = mn;
      bool stop = keep.empty() || (tol > 0 && U - Lb <= tol) || L == o.maxDepth || (tmax > 0 && now() - t0 > tmax);
      if (o.verbose) fprintf(stderr, "level %d: %llu boxes, %zu kept, [%.17g, %.17g]\n", L, (unsigned long long)n, keep.size(), Lb, U);
      if (stop) break;
      if (2 * keep.size() > cap) {
        std::sort(keep.begin(), keep.end(), [&](uint64_t a, uint64_t b) { return glo[a] < glo[b]; });
        size_t k = cap / 2;
        for (size_t t = k; t < keep.size(); t++) dropped = std::min(dropped, glo[keep[t]]);
        keep.resize(k);
      }
      uint64_t n2 = 2 * keep.size(); uint32_t vi = L % d;
      std::vector<double> nx(2 * d * n2);
      for (uint64_t t = 0; t < keep.size(); t++) {
        uint64_t i = keep[t];
        for (uint32_t j = 0; j < 2 * d; j++) { nx[j * n2 + 2 * t] = cur[j * n + i]; nx[j * n2 + 2 * t + 1] = cur[j * n + i]; }
        volatile double a = cur[(2 * vi) * n + i] * 0.5, b = cur[(2 * vi + 1) * n + i] * 0.5; double m = a + b;
        nx[(2 * vi + 1) * n2 + 2 * t] = m; nx[(2 * vi) * n2 + 2 * t + 1] = m;
      }
      cur.swap(nx); n = n2;
    }
    double t1 = now();
    double lo = mx ? -U : Lb, hi = mx ? -Lb : U;
    printf("%s f in [%.17g, %.17g] (%s, %llu boxes, depth %d, %.3f s)\n", mx ? "max" : "min", lo, hi,
           E->name(), (unsigned long long)evals, L, t1 - t0);
    printf("  attained (rigorously, at a point) %s %.17g at (", mx ? ">=" : "<=", mx ? -U : U);
    for (uint32_t j = 0; j < d; j++) printf("%s%.17g", j ? ", " : "", arg[j]);
    printf(")\n");
    return 0;
  }
  usage();
}
