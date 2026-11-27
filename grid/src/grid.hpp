/* realfp-grid: problem format, certificate output, engine interface. */
#pragma once
#include <stdint.h>
#include <string>
#include <vector>

#define RFG_MAXD 16
#define RFG_MAXT 1024   /* tape instructions (the Lean side allows 4096; GPU local memory) */

struct Problem {
  uint32_t d = 0;
  double lo[RFG_MAXD], hi[RFG_MAXD];   /* the box (binary64, as in Lean's (boxes bs).map toIC) */
  bool upper = true;                   /* f <= c (le) or c <= f (ge) */
  double c = 0;                        /* the bound (binary64 of KI.ofRat c: .lo for le, .hi for ge) */
  std::vector<double> k;               /* constants: lo, hi pairs */
  std::vector<uint32_t> code;          /* tape: op, a, b */
  uint64_t fnv = 0;                    /* FNV-1a 64 of the problem text */
  uint32_t n() const { return (uint32_t)(code.size() / 3); }
};

bool read_problem(const char *path, Problem &P, std::string &err);

struct Opts {
  int maxDepth = 0;          /* levels below the root (0: 30 per variable, at most 1000) */
  uint64_t maxBoxes = 0;     /* evaluations (0: unlimited) */
  uint64_t cap = 0;          /* boxes per level per run (0: from memory budget) */
  int threads = 0;           /* CPU threads (0: all) */
  bool verbose = false;
};

struct Stats { uint64_t boxes = 0, leaves = 0; int maxLevel = 0; };

/* One breadth-first run from a forest of R root boxes (AoS: root r, variable j at roots[2d r + 2j],
   [.. + 1]) at depth l0. flags[j] (j = level - l0) holds one byte per node of that level in BFS
   order: 0 leaf (goal proved on the box), 1 split. RUN_OVERFLOW: the next level would exceed
   `cap` boxes; flags are complete down to the last level evaluated, and `holes` gets the boxes
   (AoS, BFS order) of that level's split nodes, to be continued by the caller. */
enum RunStatus { RUN_OK = 0, RUN_OVERFLOW = 1, RUN_FAIL = 2 };
struct FailInfo { int level; double box[2 * RFG_MAXD]; double flo, fhi; };

struct Engine {
  virtual ~Engine() {}
  virtual const char *name() const = 0;
  virtual RunStatus run(const double *roots, uint64_t R, int l0, int maxLevel, uint64_t cap,
                        std::vector<std::vector<uint8_t>> &flags, std::vector<double> &holes,
                        Stats &st, FailInfo &fi) = 0;
  virtual uint64_t default_cap() = 0;
  /* Min/max exploration: evaluate n boxes (SoA, stride n: box[(2j)*n+i] = lo of var j) -> the
     enclosure of f on each box and of f at its midpoint. */
  virtual void eval_mm(const double *box, uint64_t n, double *flo, double *fhi, double *plo,
                       double *phi) = 0;
};

Engine *make_cpu(const Problem &P, const Opts &o);
Engine *make_gpu(const Problem &P, const Opts &o, bool fp32);   /* nullptr if no GPU */
bool gpu_available(std::string &desc);
