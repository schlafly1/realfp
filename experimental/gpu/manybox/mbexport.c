/* Export a manybox bisection certificate for Lean (lean/ManyBox.lean).
   usage: mbexport prob delta out.cert [gpu|cpu]
   Runs the search (GPU by default), converts the level-order split flags into a preorder
   (depth-first) bit string, 1 = split, 0 = leaf, and writes it as hex (4 bits per char,
   most significant first). Line 1 is a comment with the statistics. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>
#include "mb.h"

int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: mbexport prob delta out.cert [gpu|cpu]\n"); return 1; }
  int prob = atoi(argv[1]); double delta = atof(argv[2]);
  int gpu = !(argc > 4 && !strcmp(argv[4], "cpu"));
  double bound = prob == 0 ? 2 + delta : -delta;
  mb_cert c = {0};
  double ti = omp_get_wtime(), tinit = 0;
#ifndef MB_NO_GPU
  if (gpu) { mb_gpu_init(NULL, 0); tinit = omp_get_wtime() - ti; }   /* CUDA context: once per process */
#endif
  double t0 = omp_get_wtime();
  mb_stats s;
#ifdef MB_NO_GPU
  if (gpu) { fprintf(stderr, "built without GPU; using cpu\n"); gpu = 0; }
  s = mb_cpu_run(prob, bound, 80, omp_get_max_threads(), &c);
#else
  s = gpu ? mb_gpu_run(prob, bound, 80, &c) : mb_cpu_run(prob, bound, 80, omp_get_max_threads(), &c);
#endif
  double t1 = omp_get_wtime();
  if (!s.ok) { fprintf(stderr, "claim not proved (%llu unresolved)\n", (unsigned long long)s.unresolved); return 2; }
  /* level offsets and, per level, the rank of each split box */
  uint64_t *lvoff = calloc(s.levels + 1, 8);
  { uint64_t n = 1, o = 0; for (int l = 0; l < s.levels; l++) { lvoff[l] = o; uint64_t nf = 0; for (uint64_t i = 0; i < n; i++) nf += c.flags[o + i]; o += n; n = 2 * nf; } lvoff[s.levels] = o; }
  uint32_t *rank = malloc(c.len * 4);
  for (int l = 0; l < s.levels; l++) { uint32_t r = 0; for (uint64_t i = lvoff[l]; i < lvoff[l + 1]; i++) { rank[i] = r; r += c.flags[i]; } }
  /* iterative preorder walk: stack of (level, index in level) */
  uint8_t *dfs = malloc(c.len); uint64_t nd = 0;
  struct { int l; uint64_t i; } st[128]; int sp = 0;
  st[sp].l = 0; st[sp].i = 0; sp++;
  while (sp) {
    sp--; int l = st[sp].l; uint64_t i = st[sp].i, g = lvoff[l] + i;
    uint8_t f = c.flags[g]; dfs[nd++] = f;
    if (f) { uint64_t ch = 2ull * rank[g];
      st[sp].l = l + 1; st[sp].i = ch + 1; sp++;   /* right pushed first */
      st[sp].l = l + 1; st[sp].i = ch; sp++; }
  }
  if (nd != c.len) { fprintf(stderr, "internal: preorder length %llu != %llu\n", (unsigned long long)nd, (unsigned long long)c.len); return 3; }
  double t2 = omp_get_wtime();
  FILE *fo = fopen(argv[3], "w");
  fprintf(fo, "# manybox prob %d delta %.17g dim %d nodes %llu leaves %llu levels %d search %s %.6f s\n", prob, delta, mb_dim(prob),
          (unsigned long long)s.evals, (unsigned long long)s.leaves, s.levels, gpu ? "gpu" : "cpu", t1 - t0);
  static const char hx[] = "0123456789abcdef";
  for (uint64_t i = 0; i < nd; i += 4) {
    int v = 0; for (int k = 0; k < 4; k++) v = 2 * v + (i + k < nd ? dfs[i + k] : 0);
    fputc(hx[v], fo);
  }
  fputc('\n', fo); fclose(fo);
  double t3 = omp_get_wtime();
  printf("prob %d delta %g: %llu nodes, %llu leaves; CUDA init %.1f ms, search (%s, incl. flag copy) %.3f ms, preorder %.3f ms, write %.3f ms -> %s\n",
         prob, delta, (unsigned long long)s.evals, (unsigned long long)s.leaves, tinit * 1e3, gpu ? "gpu" : "cpu",
         (t1 - t0) * 1e3, (t2 - t1) * 1e3, (t3 - t2) * 1e3, argv[3]);
  return 0;
}
