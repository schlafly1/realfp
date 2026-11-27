/* manybox v2 driver.
   mb2 search  PROB PREC DELTA BACKEND [MAXLEVEL] [REPS]   BACKEND = gpu | cpu1 | cpuN (N threads)
   mb2 export  PROB PREC DELTA OUT.cert [gpu|cpu]           one certificate (preorder hex)
   mb2 split   PROB PREC DELTA K OUTDIR [gpu|cpu]           top tree to depth K + one certificate per sub-box
   mb2 refute  PROB PREC BOUND [gpu|cpu]                    look for a box on which the claim fails everywhere
   mb2 sample  PROB CERT|DIR K SEED                         K random leaves (uniform over leaves)
   PREC = 64 | 32 (32: GPU only). DELTA is the margin (bound = base + delta for f <= bound claims,
   base - delta for f >= bound claims); `refute` takes the bound itself. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <string>
#include <vector>
#include <random>
#include <omp.h>
#include <sys/stat.h>
#include "mb2.hpp"

static double now() { return omp_get_wtime(); }
static int find_prob(const char *s) {
  for (int p = 0; p < MB_NPROB; p++) if (!strcmp(s, MB2_NAME[p])) return p;
  int p = atoi(s); if (p < 0 || p >= MB_NPROB) { fprintf(stderr, "unknown problem %s\n", s); exit(1); }
  return p;
}
static double bound_of(int p, double delta) { return MB2_BASE[p] + (MB2_UPPER[p] ? delta : -delta); }
static mb2_forest root_forest(int d) { mb2_forest f; f.level = 0; f.n = 1; for (int j = 0; j < d; j++) f.c[j].assign(1, 0); return f; }

static mb2_stats run(const mb2_opts &o, const mb2_forest &f, int gpu, std::vector<uint8_t> *fl) {
#ifdef MB2_NO_GPU
  (void)gpu; return mb2_cpu(o, f, fl);
#else
  return gpu ? mb2_gpu(o, f, fl) : mb2_cpu(o, f, fl);
#endif
}
static void check_consts(int prec) {
  if (prec != 32) return;
  for (double c : MB2_CONSTS) if ((double)(float)c != c) { fprintf(stderr, "constant %g not exact in binary32\n", c); exit(1); }
}
static mb2_opts opts(int p, int prec, double bound, int maxlevel, int T) {
  mb2_opts o; o.prob = p; o.prec = prec; o.bound = bound; o.cap = 0; o.nthreads = T;
  int d = MB2_DIM[p];
  int lim = prec == 32 ? 23 * d + 1 : 52 * d + 1;      /* endpoints exact */
  if (lim > 31 * d + 1) lim = 31 * d + 1;              /* uint32 coordinates */
  o.maxlevel = maxlevel > 0 && maxlevel < lim ? maxlevel : lim;
  if (getenv("MB2_CAP")) o.cap = strtoull(getenv("MB2_CAP"), 0, 10);
  return o;
}
static void print_stats(const char *tag, const mb2_stats &s, double t) {
  printf("%s: ok %d levels %d evals %llu leaves %llu unresolved %llu refuted %llu peak %llu time %.6f s (%.3g boxes/s)\n",
         tag, s.ok, s.levels, (unsigned long long)s.evals, (unsigned long long)s.leaves, (unsigned long long)s.unresolved,
         (unsigned long long)s.refuted, (unsigned long long)s.peak, t, s.evals / t);
  fflush(stdout);
}

/* level-order flags of a forest of nroots -> preorder bits; start[r] = offset of root r */
static std::vector<uint8_t> preorder(const std::vector<uint8_t> &fl, uint64_t nroots, std::vector<uint64_t> *start) {
  std::vector<uint64_t> lvoff; std::vector<uint32_t> rank(fl.size());
  { uint64_t n = nroots, o = 0; while (n && o < fl.size()) { lvoff.push_back(o); uint64_t nf = 0, r = 0;
      for (uint64_t i = 0; i < n; i++) { rank[o + i] = (uint32_t)r; r += fl[o + i]; nf += fl[o + i]; } o += n; n = 2 * nf; }
    lvoff.push_back(o); }
  std::vector<uint8_t> out; out.reserve(fl.size());
  std::vector<std::pair<int, uint64_t>> st;
  for (uint64_t r = nroots; r-- > 0;) st.push_back({0, r});
  if (start) start->assign(nroots, 0);
  while (!st.empty()) {
    auto [l, i] = st.back(); st.pop_back();
    if (l == 0 && start) (*start)[i] = out.size();
    uint64_t g = lvoff[l] + i; uint8_t f = fl[g]; out.push_back(f);
    if (f) { uint64_t ch = 2ull * rank[g]; st.push_back({l + 1, ch + 1}); st.push_back({l + 1, ch}); }
  }
  return out;
}
static void write_hex(FILE *fo, const uint8_t *b, uint64_t n) {
  static const char hx[] = "0123456789abcdef";
  for (uint64_t i = 0; i < n; i += 4) { int v = 0; for (int k = 0; k < 4; k++) v = 2 * v + (i + k < n ? b[i + k] : 0); fputc(hx[v], fo); }
  fputc('\n', fo);
}
static uint64_t fnv(const uint8_t *p, uint64_t n) { uint64_t h = 1469598103934665603ull; for (uint64_t i = 0; i < n; i++) { h ^= p[i]; h *= 1099511628211ull; } return h; }
static uint64_t dbits(double x) { uint64_t u; memcpy(&u, &x, 8); return u; }

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "see the comment at the top of mb2.cpp\n"); return 1; }
  std::string mode = argv[1];
  int p = find_prob(argv[2]), d = MB2_DIM[p];
  if (mode == "search") {
    int prec = atoi(argv[3]); double delta = atof(argv[4]); std::string be = argv[5];
    int maxl = argc > 6 ? atoi(argv[6]) : 0, reps = argc > 7 ? atoi(argv[7]) : 1;
    check_consts(prec);
    int gpu = be == "gpu", T = gpu ? 1 : atoi(be.c_str() + 3);
    if (!gpu && prec != 64) { fprintf(stderr, "CPU engine is fp64 only\n"); return 1; }
    mb2_opts o = opts(p, prec, bound_of(p, delta), maxl, T);
#ifndef MB2_NO_GPU
    if (gpu) { double t0 = now(); char nm[128]; mb2_gpu_init(nm, sizeof nm); printf("GPU %s, init %.3f s\n", nm, now() - t0); }
#endif
    for (int r = 0; r < reps; r++) {
      double t0 = now(); mb2_stats s = run(o, root_forest(d), gpu, NULL); double t = now() - t0;
      char tag[160]; snprintf(tag, sizeof tag, "%s delta %g fp%d %s", MB2_NAME[p], delta, prec, be.c_str());
      print_stats(tag, s, t);
    }
    return 0;
  }
  if (mode == "refute") {
    int prec = atoi(argv[3]); double bound = atof(argv[4]); int gpu = !(argc > 5 && !strcmp(argv[5], "cpu"));
    check_consts(prec);
    mb2_opts o = opts(p, prec, bound, 0, 0);
    double t0 = now(); mb2_stats s = run(o, root_forest(d), gpu, NULL); double t = now() - t0;
    print_stats("refute", s, t);
    if (s.refuted) {
      printf("refuted box level %d coords", s.ref_level);
      for (int j = 0; j < d; j++) printf(" %u", s.ref_c[j]);
      printf("\nbox");
      for (int j = 0; j < d; j++) {
        int sj = mb2_splits(d, s.ref_level, j); double h = ldexp(2.0, -sj);
        printf(" [%.17g, %.17g]", -1 + s.ref_c[j] * h, -1 + (s.ref_c[j] + 1.0) * h);
      }
      printf("\n");
    }
    return 0;
  }
  if (mode == "export") {
    int prec = atoi(argv[3]); double delta = atof(argv[4]); const char *out = argv[5];
    int gpu = !(argc > 6 && !strcmp(argv[6], "cpu"));
    check_consts(prec);
    mb2_opts o = opts(p, prec, bound_of(p, delta), 0, 0); o.cap = 1ull << 31;
    std::vector<uint8_t> fl;
    double t0 = now(); mb2_stats s = run(o, root_forest(d), gpu, &fl); double t1 = now();
    print_stats("export search", s, t1 - t0);
    if (s.ok != 1) { fprintf(stderr, "claim not proved\n"); return 2; }
    std::vector<uint8_t> pre = preorder(fl, 1, NULL);
    FILE *fo = fopen(out, "w");
    fprintf(fo, "# manybox2 prob %s delta %.17g prec %d dim %d nodes %llu leaves %llu levels %d search %s %.6f s fnv %016llx\n",
            MB2_NAME[p], delta, prec, d, (unsigned long long)s.evals, (unsigned long long)s.leaves, s.levels, gpu ? "gpu" : "cpu",
            t1 - t0, (unsigned long long)fnv(pre.data(), pre.size()));
    write_hex(fo, pre.data(), pre.size()); fclose(fo);
    printf("wrote %s (%llu nodes) in %.3f s\n", out, (unsigned long long)pre.size(), now() - t1);
    return 0;
  }
  if (mode == "split") {
    int prec = atoi(argv[3]); double delta = atof(argv[4]); int K = atoi(argv[5]); std::string dir = argv[6];
    int gpu = !(argc > 7 && !strcmp(argv[7], "cpu"));
    check_consts(prec);
    mkdir(dir.c_str(), 0755);
    mb2_opts o = opts(p, prec, bound_of(p, delta), K, 0); o.cap = 1ull << 31;
    std::vector<uint8_t> fl;
    double t0 = now(); mb2_stats top = run(o, root_forest(d), gpu, &fl);
    if (top.refuted) { fprintf(stderr, "refuted\n"); return 2; }
    /* replay the top levels on the host: coordinates of every top node, level order */
    std::vector<std::vector<uint32_t>> C(d); std::vector<int> L;
    { std::vector<std::vector<uint32_t>> cur(d, std::vector<uint32_t>(1, 0)); uint64_t o0 = 0;
      for (int l = 0; l <= K && !cur[0].empty(); l++) {
        uint64_t n = cur[0].size();
        for (uint64_t i = 0; i < n; i++) { for (int j = 0; j < d; j++) C[j].push_back(cur[j][i]); L.push_back(l); }
        if (l == K) break;
        std::vector<std::vector<uint32_t>> nx(d);
        for (uint64_t i = 0; i < n; i++) if (fl[o0 + i])
          for (int j = 0; j < d; j++) { uint32_t c = cur[j][i]; if (j == l % d) { nx[j].push_back(2 * c); nx[j].push_back(2 * c + 1); } else { nx[j].push_back(c); nx[j].push_back(c); } }
        o0 += n; cur.swap(nx);
      } }
    uint64_t ntop = fl.size(), nall = L.size();     /* nodes at levels < K have flags; level-K nodes are roots */
    std::vector<uint8_t> tfl(nall, 0); for (uint64_t i = 0; i < ntop; i++) tfl[i] = fl[i];
    for (uint64_t i = ntop; i < nall; i++) tfl[i] = 2;   /* placeholder */
    /* preorder of the top tree (level order -> preorder; 2 = sub-box root) */
    std::vector<uint64_t> lvoff; std::vector<uint32_t> rank(nall);
    { uint64_t n = 1, o1 = 0; while (n && o1 < nall) { lvoff.push_back(o1); uint64_t r = 0;
        for (uint64_t i = 0; i < n; i++) { rank[o1 + i] = (uint32_t)r; r += tfl[o1 + i] == 1; } o1 += n; n = 2 * r; } lvoff.push_back(o1); }
    std::vector<uint64_t> order;
    { std::vector<std::pair<int, uint64_t>> st = {{0, 0}};
      while (!st.empty()) { auto [l, i] = st.back(); st.pop_back(); uint64_t g = lvoff[l] + i; order.push_back(g);
        if (tfl[g] == 1) { uint64_t ch = 2ull * rank[g]; st.push_back({l + 1, ch + 1}); st.push_back({l + 1, ch}); } } }
    FILE *ft = fopen((dir + "/top.txt").c_str(), "w");
    fprintf(ft, "# manybox2 split prob %s delta %.17g prec %d dim %d K %d\n", MB2_NAME[p], delta, prec, d, K);
    uint64_t nj = 0, tot_nodes = 0, tot_leaves = top.leaves; double tsub = 0;
    std::vector<uint8_t> sfl; uint64_t hall = 1469598103934665603ull;
    for (uint64_t g : order) {
      int l = L[g];
      if (tfl[g] == 1) {
        int i = l % d, s = mb2_splits(d, l, i);
        double m = -1.0 + (2.0 * C[i][g] + 1.0) * ldexp(1.0, -s);
        fprintf(ft, "S %d %llu\n", i, (unsigned long long)dbits(m));
        continue;
      }
      fprintf(ft, "J %d", l); for (int j = 0; j < d; j++) fprintf(ft, " %u", C[j][g]);
      if (tfl[g] == 0) { fprintf(ft, " 0\n"); nj++; continue; }   /* proved at the top */
      mb2_forest f; f.level = l; f.n = 1; for (int j = 0; j < d; j++) f.c[j].assign(1, C[j][g]);
      mb2_opts os = opts(p, prec, bound_of(p, delta), 0, 0); os.cap = 1ull << 31;
      sfl.clear(); double ta = now(); mb2_stats s = run(os, f, gpu, &sfl); tsub += now() - ta;
      if (s.ok != 1) { fprintf(stderr, "sub-box %llu not proved (ok %d)\n", (unsigned long long)nj, s.ok); return 2; }
      std::vector<uint8_t> pre = preorder(sfl, 1, NULL);
      char fn[64]; snprintf(fn, sizeof fn, "job%05llu.cert", (unsigned long long)nj);
      FILE *fo = fopen((dir + "/" + fn).c_str(), "w");
      uint64_t h = fnv(pre.data(), pre.size()); hall ^= h; hall *= 1099511628211ull;
      fprintf(fo, "# manybox2 sub prob %s level %d nodes %llu leaves %llu fnv %016llx\n", MB2_NAME[p], l,
              (unsigned long long)pre.size(), (unsigned long long)s.leaves, (unsigned long long)h);
      write_hex(fo, pre.data(), pre.size()); fclose(fo);
      fprintf(ft, " %s\n", fn); nj++; tot_nodes += pre.size(); tot_leaves += s.leaves;
    }
    fclose(ft);
    printf("split %s delta %g fp%d K %d: %llu top nodes, %llu jobs, %llu sub-box nodes, %llu leaves total; search %.3f s (sub-boxes %.3f s) fnv %016llx\n",
           MB2_NAME[p], delta, prec, K, (unsigned long long)ntop, (unsigned long long)nj, (unsigned long long)tot_nodes,
           (unsigned long long)tot_leaves, now() - t0, tsub, (unsigned long long)hall);
    return 0;
  }
  if (mode == "sample") {
    /* uniform sample of K leaves (reservoir) of a certificate or a split directory */
    std::string src = argv[3]; uint64_t K = strtoull(argv[4], 0, 10); uint64_t seed = strtoull(argv[5], 0, 10);
    std::mt19937_64 rng(seed);
    struct Leaf { int l; uint32_t c[MB2_MAXD]; };
    std::vector<Leaf> res; uint64_t seen = 0;
    auto offer = [&](int l, const uint32_t *c) {
      Leaf x; x.l = l; memcpy(x.c, c, sizeof(uint32_t) * d); seen++;
      if (res.size() < K) res.push_back(x);
      else { uint64_t r = rng() % seen; if (r < K) res[r] = x; }
    };
    auto walk = [&](const std::string &hex, int l0, const uint32_t *c0) {
      /* iterative decC: stack of (level, coords) */
      struct N { int l; uint32_t c[MB2_MAXD]; }; std::vector<N> st; N r; r.l = l0; memcpy(r.c, c0, sizeof r.c); st.push_back(r);
      uint64_t pos = 0;
      auto bit = [&](uint64_t i) { uint64_t j = i / 4; if (j >= hex.size()) return 0; char ch = hex[j];
        int v = ch >= '0' && ch <= '9' ? ch - '0' : (ch >= 'a' && ch <= 'f' ? ch - 'a' + 10 : 0); return (v >> (3 - i % 4)) & 1; };
      while (!st.empty()) { N n = st.back(); st.pop_back();
        if (!bit(pos++)) { offer(n.l, n.c); continue; }
        int i = n.l % d; N a = n, b = n; a.l = b.l = n.l + 1; a.c[i] = 2 * n.c[i]; b.c[i] = 2 * n.c[i] + 1;
        st.push_back(b); st.push_back(a); }
    };
    auto readhex = [](const std::string &fn) { FILE *f = fopen(fn.c_str(), "r"); std::string s, line; char buf[1 << 16];
      if (!f) { fprintf(stderr, "cannot read %s\n", fn.c_str()); exit(1); }
      bool body = false; int ch; std::string cur;
      while ((ch = fgetc(f)) != EOF) { if (ch == '\n') { if (!cur.empty() && cur[0] != '#') { s = cur; body = true; break; } cur.clear(); } else cur.push_back((char)ch); }
      if (!body && !cur.empty() && cur[0] != '#') s = cur;
      (void)buf; (void)line; fclose(f); return s; };
    struct stat sb; uint32_t zero[MB2_MAXD] = {0};
    if (stat(src.c_str(), &sb) == 0 && S_ISDIR(sb.st_mode)) {
      FILE *ft = fopen((src + "/top.txt").c_str(), "r"); char line[4096];
      while (fgets(line, sizeof line, ft)) {
        if (line[0] != 'J') continue;
        char *q = line + 2; int l = strtol(q, &q, 10); uint32_t c[MB2_MAXD];
        for (int j = 0; j < d; j++) c[j] = (uint32_t)strtoul(q, &q, 10);
        while (*q == ' ') q++; std::string fn(q); while (!fn.empty() && (fn.back() == '\n' || fn.back() == ' ')) fn.pop_back();
        if (fn == "0") offer(l, c); else walk(readhex(src + "/" + fn), l, c);
      }
      fclose(ft);
    } else walk(readhex(src), 0, zero);
    printf("# %llu leaves seen, %zu sampled (seed %llu)\n", (unsigned long long)seen, res.size(), (unsigned long long)seed);
    for (auto &x : res) { printf("%d", x.l); for (int j = 0; j < d; j++) printf(" %u", x.c[j]); printf("\n"); }
    return 0;
  }
  fprintf(stderr, "unknown mode\n"); return 1;
}
