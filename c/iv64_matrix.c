/* Lean wrappers for the Interval64 matrix kernels (c/iv64_matrix.h). */
#define _GNU_SOURCE
#include <lean/lean.h>
#include <string.h>
#include "iv64_matrix.h"

/* Copy a FloatArray into a dense buffer of length m, reading 0 past its end
   (the spec's `fget`). */
static void ivm_pad(b_lean_obj_arg a, double *dst, size_t m) {
  size_t sz = lean_sarray_size(a);
  const double *src = lean_float_array_cptr(a);
  size_t c = sz < m ? sz : m;
  memcpy(dst, src, c * sizeof(double));
  for (size_t k = c; k < m; k++) dst[k] = 0.0;
}

/* Interval64.Mat.pdMarginsImpl (M : @& IMat) (X : @& FloatArray) : FloatArray */
LEAN_EXPORT lean_obj_res iv64_pd_margins(b_lean_obj_arg M, b_lean_obj_arg X) {
  b_lean_obj_arg nobj = lean_ctor_get(M, 0);
  if (!lean_is_scalar(nobj)) lean_internal_panic("iv64_pd_margins: matrix too large");
  size_t n = lean_unbox(nobj);
  if (n > (1u << 15)) lean_internal_panic("iv64_pd_margins: matrix too large");
  size_t m = n * n;
  double *alo = (double *)malloc(sizeof(double) * (m ? m : 1));
  double *ahi = (double *)malloc(sizeof(double) * (m ? m : 1));
  double *x = (double *)malloc(sizeof(double) * (m ? m : 1));
  if (!alo || !ahi || !x) lean_internal_panic_out_of_memory();
  ivm_pad(lean_ctor_get(M, 1), alo, m);
  ivm_pad(lean_ctor_get(M, 2), ahi, m);
  ivm_pad(X, x, m);
  lean_object *r = lean_alloc_sarray(sizeof(double), 2 * n, 2 * n);
  if (iv64m_pd_margins(n, alo, ahi, x, lean_float_array_cptr(r)) != 0)
    lean_internal_panic_out_of_memory();
  free(alo); free(ahi); free(x);
  return r;
}
