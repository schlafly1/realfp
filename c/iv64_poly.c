/* Lean wrappers for the polynomial, Bernstein and quadrature kernels
   (c/iv64_poly.h, c/iv64_quad.h). Each `iv64_*` function below is attached with
   `@[implemented_by]` to the Lean specification named in its comment. */
#define _GNU_SOURCE
#include <lean/lean.h>
#include <string.h>
#include "iv64_quad.h"

static size_t ivw_nat(b_lean_obj_arg n) { return lean_is_scalar(n) ? lean_unbox(n) : SIZE_MAX; }

static void *ivw_alloc(size_t n, size_t sz) {
  void *p = malloc((n ? n : 1) * sz);
  if (!p) lean_internal_panic_out_of_memory();
  return p;
}

/* IPoly (Array Interval64) → dense array */
static ivp_t *ivw_poly(b_lean_obj_arg P, size_t *n) {
  size_t m = lean_array_size(P);
  ivp_t *p = (ivp_t *)ivw_alloc(m, sizeof(ivp_t));
  for (size_t i = 0; i < m; i++) p[i] = ivt_unbox(lean_array_get_core(P, i));
  *n = m;
  return p;
}

typedef struct { ivp2_t P; ivp_t **rows; size_t *sz; size_t maxsz; } ivw_poly2;
static void ivw_poly2_read(b_lean_obj_arg P, ivw_poly2 *w) {
  size_t n = lean_array_size(P);
  w->rows = (ivp_t **)ivw_alloc(n, sizeof(ivp_t *));
  w->sz = (size_t *)ivw_alloc(n, sizeof(size_t));
  w->maxsz = 0;
  for (size_t j = 0; j < n; j++) {
    w->rows[j] = ivw_poly(lean_array_get_core(P, j), &w->sz[j]);
    if (w->sz[j] > w->maxsz) w->maxsz = w->sz[j];
  }
  w->P = (ivp2_t){ (const ivp_t *const *)w->rows, w->sz, n };
}
static void ivw_poly2_free(ivw_poly2 *w) {
  for (size_t j = 0; j < w->P.n; j++) free(w->rows[j]);
  free(w->rows); free(w->sz);
}

/* IPoly.eval */
LEAN_EXPORT lean_obj_res iv64_poly_eval(b_lean_obj_arg P, b_lean_obj_arg X) {
  size_t n; ivp_t *p = ivw_poly(P, &n);
  ivp_t r = ivp_eval(p, n, ivt_unbox(X));
  free(p);
  return ivt_box(r);
}

/* IPoly.evalMV */
LEAN_EXPORT lean_obj_res iv64_poly_eval_mv(b_lean_obj_arg P, b_lean_obj_arg dP, b_lean_obj_arg X) {
  size_t n, dn; ivp_t *p = ivw_poly(P, &n), *dp = ivw_poly(dP, &dn);
  ivp_t r = ivp_eval_mv(p, n, dp, dn, ivt_unbox(X));
  free(p); free(dp);
  return ivt_box(r);
}

/* IPoly.rangeAux */
LEAN_EXPORT lean_obj_res iv64_poly_range_aux(b_lean_obj_arg P, b_lean_obj_arg dP, b_lean_obj_arg fuel,
                                             b_lean_obj_arg X) {
  size_t n, dn; ivp_t *p = ivw_poly(P, &n), *dp = ivw_poly(dP, &dn);
  ivp_t r = ivp_range_aux(p, n, dp, dn, ivw_nat(fuel), ivt_unbox(X));
  free(p); free(dp);
  return ivt_box(r);
}

/* IPoly.checkAux with the goal predicate `mode` (0: c ≤ lo, 1: c < lo, 2: hi ≤ c, 3: hi < c) */
LEAN_EXPORT uint8_t iv64_poly_check(b_lean_obj_arg P, b_lean_obj_arg dP, uint8_t mode, double c,
                                    b_lean_obj_arg fuel, b_lean_obj_arg X) {
  size_t n, dn; ivp_t *p = ivw_poly(P, &n), *dp = ivw_poly(dP, &dn);
  int r = ivp_check_aux(p, n, dp, dn, mode, c, ivw_nat(fuel), ivt_unbox(X));
  free(p); free(dp);
  return (uint8_t)r;
}

/* IPoly2.eval2 */
LEAN_EXPORT lean_obj_res iv64_poly2_eval(b_lean_obj_arg P, b_lean_obj_arg X, b_lean_obj_arg Y) {
  ivw_poly2 w; ivw_poly2_read(P, &w);
  ivp_t r = ivp_eval2(w.P, ivt_unbox(X), ivt_unbox(Y));
  ivw_poly2_free(&w);
  return ivt_box(r);
}

/* IPoly2.checkAux2 */
LEAN_EXPORT uint8_t iv64_poly2_check(b_lean_obj_arg P, uint8_t mode, double c, b_lean_obj_arg fuel,
                                     b_lean_obj_arg X, b_lean_obj_arg Y) {
  ivw_poly2 w; ivw_poly2_read(P, &w);
  int r = ivp_check_aux2(w.P, mode, c, ivw_nat(fuel), ivt_unbox(X), ivt_unbox(Y));
  ivw_poly2_free(&w);
  return (uint8_t)r;
}

/* IPoly.bernOn (caller: bernDeg P n ≤ 56) */
LEAN_EXPORT lean_obj_res iv64_bern_on(b_lean_obj_arg P, b_lean_obj_arg X, b_lean_obj_arg deg) {
  size_t n; ivp_t *p = ivw_poly(P, &n);
  ivp_t *buf = (ivp_t *)ivw_alloc(2 * n, sizeof(ivp_t));
  ivp_t r = ivp_bern_on(p, n, ivt_unbox(X), ivw_nat(deg), buf);
  free(p); free(buf);
  return ivt_box(r);
}

/* IPoly.bernRange */
LEAN_EXPORT lean_obj_res iv64_bern_range(b_lean_obj_arg P, b_lean_obj_arg deg, b_lean_obj_arg fuel,
                                         b_lean_obj_arg X) {
  size_t n; ivp_t *p = ivw_poly(P, &n);
  ivp_t *buf = (ivp_t *)ivw_alloc(2 * n, sizeof(ivp_t));
  ivp_t r = ivp_bern_range(p, n, ivw_nat(deg), ivw_nat(fuel), ivt_unbox(X), buf);
  free(p); free(buf);
  return ivt_box(r);
}

/* IPoly.checkAuxB */
LEAN_EXPORT uint8_t iv64_bern_check(b_lean_obj_arg P, b_lean_obj_arg deg, uint8_t mode, double c,
                                    b_lean_obj_arg fuel, b_lean_obj_arg X) {
  size_t n; ivp_t *p = ivw_poly(P, &n);
  ivp_t *buf = (ivp_t *)ivw_alloc(2 * n, sizeof(ivp_t));
  int r = ivp_bern_check(p, n, ivw_nat(deg), mode, c, ivw_nat(fuel), ivt_unbox(X), buf);
  free(p); free(buf);
  return (uint8_t)r;
}

static void ivw_work2(ivw_poly2 *w, ivp2_work_t *k) {
  size_t ms = w->maxsz ? w->maxsz : 1, n = w->P.n ? w->P.n : 1;
  k->maxsz = ms;
  k->q = (ivp_t *)ivw_alloc(n * ms, sizeof(ivp_t));
  k->tmp = (ivp_t *)ivw_alloc(2 * ms, sizeof(ivp_t));
  k->col = (ivp_t *)ivw_alloc(n, sizeof(ivp_t));
  k->buf1 = (ivp_t *)ivw_alloc(2 * n, sizeof(ivp_t));
}
static void ivw_work2_free(ivp2_work_t *k) { free(k->q); free(k->tmp); free(k->col); free(k->buf1); }

/* IPoly2.bern2On */
LEAN_EXPORT lean_obj_res iv64_bern2_on(b_lean_obj_arg P, b_lean_obj_arg X, b_lean_obj_arg Y,
                                       b_lean_obj_arg n, b_lean_obj_arg m) {
  ivw_poly2 w; ivw_poly2_read(P, &w);
  ivp2_work_t k; ivw_work2(&w, &k);
  ivp_t r = ivp_bern2_on(w.P, ivt_unbox(X), ivt_unbox(Y), ivw_nat(n), ivw_nat(m), &k);
  ivw_work2_free(&k); ivw_poly2_free(&w);
  return ivt_box(r);
}

/* IPoly2.checkAux2B */
LEAN_EXPORT uint8_t iv64_bern2_check(b_lean_obj_arg P, b_lean_obj_arg n, b_lean_obj_arg m, uint8_t mode,
                                     double c, b_lean_obj_arg fuel, b_lean_obj_arg X, b_lean_obj_arg Y) {
  ivw_poly2 w; ivw_poly2_read(P, &w);
  ivp2_work_t k; ivw_work2(&w, &k);
  int r = ivp_bern2_check(w.P, ivw_nat(n), ivw_nat(m), mode, c, ivw_nat(fuel), ivt_unbox(X),
                          ivt_unbox(Y), &k);
  ivw_work2_free(&k); ivw_poly2_free(&w);
  return (uint8_t)r;
}

/* ---------- tapes ---------- */

static void ivw_tape(ivt_t *t, b_lean_obj_arg code, b_lean_obj_arg consts, b_lean_obj_arg fns,
                     b_lean_obj_arg atan2fn) {
  t->code = (const uint32_t *)lean_sarray_cptr(code);
  t->len = lean_sarray_size(code) / 12;
  t->k = lean_float_array_cptr(consts);
  t->fns = fns;
  t->atan2fn = atan2fn;
  t->regs = (ivp_t *)ivw_alloc(t->len, sizeof(ivp_t));
}

/* Quad.integrateE0 / integrateE1 (order 0 / 1): ∫_a^b e(x) dx, `e` = register rF, `e.diff 0` = rD */
LEAN_EXPORT lean_obj_res iv64_quad_integrate(b_lean_obj_arg code, b_lean_obj_arg consts,
                                             b_lean_obj_arg fns, b_lean_obj_arg atan2fn, uint32_t rF,
                                             uint32_t rD, uint8_t order, double a, double b, double tol,
                                             b_lean_obj_arg fuel) {
  ivt_t t; ivw_tape(&t, code, consts, fns, atan2fn);
  ivq_ctx q = { &t, order, 0, { { 0, 0 }, { 0, 0 } }, 1, rF, rD, NULL, 0, 0, 0, 0 };
  ivp_t r = ivq_integrate(&q, a, b, tol, ivw_nat(fuel));
  free(t.regs);
  return ivt_box(r);
}

/* Quad.integrate2E0 / integrate2E1 (inner order 0 / 1 in y = var 1, outer cell0 in x = var 0) */
LEAN_EXPORT lean_obj_res iv64_quad_integrate2(b_lean_obj_arg code, b_lean_obj_arg consts,
                                              b_lean_obj_arg fns, b_lean_obj_arg atan2fn, uint32_t rF,
                                              uint32_t rD, uint8_t order, double a, double b, double c,
                                              double d, double tol, b_lean_obj_arg fuel) {
  ivt_t t; ivw_tape(&t, code, consts, fns, atan2fn);
  size_t f = ivw_nat(fuel);
  ivq_ctx in = { &t, order, 1, { { 0, 0 }, { 0, 0 } }, 2, rF, rD, NULL, c, d, tol, f };
  ivq_ctx out = { NULL, 0, 0, { { 0, 0 }, { 0, 0 } }, 1, 0, 0, &in, 0, 0, 0, 0 };
  ivp_t r = ivq_integrate(&out, a, b, tol, f);
  free(t.regs);
  return ivt_box(r);
}

/* KQ.quadF: Σ over cells (lo, m, hi) (FloatArray of triples) of the Taylor cell enclosures;
   roots = registers of d_0 .. d_K (ByteArray of u32). */
LEAN_EXPORT lean_obj_res iv64_quad_taylor(b_lean_obj_arg code, b_lean_obj_arg consts, b_lean_obj_arg fns,
                                          b_lean_obj_arg atan2fn, b_lean_obj_arg roots,
                                          b_lean_obj_arg cells) {
  ivt_t t; ivw_tape(&t, code, consts, fns, atan2fn);
  size_t nr = lean_sarray_size(roots) / 4;
  const uint32_t *r32 = (const uint32_t *)lean_sarray_cptr(roots);
  size_t K = nr - 1;
  size_t *rs = (size_t *)ivw_alloc(nr, sizeof(size_t));
  for (size_t j = 0; j < nr; j++) rs[j] = r32[j];
  ivp_t *tmp = (ivp_t *)ivw_alloc(K, sizeof(ivp_t));
  size_t nc = lean_sarray_size(cells) / 3;
  const double *cs = lean_float_array_cptr(cells);
  ivp_t *cv = (ivp_t *)ivw_alloc(nc, sizeof(ivp_t));
  for (size_t i = 0; i < nc; i++)
    cv[i] = ivq_taylor_cell(&t, rs, K, cs[3 * i], cs[3 * i + 1], cs[3 * i + 2], tmp);
  ivp_t acc = ivp_zero();
  for (size_t i = nc; i-- > 0;) acc = ivp_add(cv[i], acc);
  free(cv); free(tmp); free(rs); free(t.regs);
  return ivt_box(acc);
}

/* One Taylor cell (KQ.cellF), for adaptive partition search. */
LEAN_EXPORT lean_obj_res iv64_quad_taylor_cell(b_lean_obj_arg code, b_lean_obj_arg consts,
                                               b_lean_obj_arg fns, b_lean_obj_arg atan2fn,
                                               b_lean_obj_arg roots, double lo, double m, double hi) {
  ivt_t t; ivw_tape(&t, code, consts, fns, atan2fn);
  size_t nr = lean_sarray_size(roots) / 4;
  const uint32_t *r32 = (const uint32_t *)lean_sarray_cptr(roots);
  size_t K = nr - 1;
  size_t *rs = (size_t *)ivw_alloc(nr, sizeof(size_t));
  for (size_t j = 0; j < nr; j++) rs[j] = r32[j];
  ivp_t *tmp = (ivp_t *)ivw_alloc(K, sizeof(ivp_t));
  ivp_t r = ivq_taylor_cell(&t, rs, K, lo, m, hi, tmp);
  free(tmp); free(rs); free(t.regs);
  return ivt_box(r);
}

/* Tape evaluation (KF.evalI env e at register `root`), for tests and benchmarks. */
LEAN_EXPORT lean_obj_res iv64_tape_eval(b_lean_obj_arg code, b_lean_obj_arg consts, b_lean_obj_arg fns,
                                        b_lean_obj_arg atan2fn, uint32_t root, b_lean_obj_arg env) {
  ivt_t t; ivw_tape(&t, code, consts, fns, atan2fn);
  size_t ne = lean_array_size(env);
  ivp_t *e = (ivp_t *)ivw_alloc(ne, sizeof(ivp_t));
  for (size_t i = 0; i < ne; i++) e[i] = ivt_unbox(lean_array_get_core(env, i));
  ivp_t r = ivt_eval(&t, e, ne, root);
  free(e); free(t.regs);
  return ivt_box(r);
}
