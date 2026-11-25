/* Lean FFI shim for libivgpu (see IvGpu.lean). */
#include <lean/lean.h>
#include "../ivgpu.h"

static lean_obj_res io_err(const char *m) {
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(m)));
}

LEAN_EXPORT lean_obj_res lean_ivgpu_grid(uint32_t fn, uint32_t k, lean_obj_arg w) {
  red_t r; float ms = 0;
  if (fn > 1 || k > 13 || ivgpu_grid((int)fn, (int)k, 64, &r, &ms)) return io_err("ivgpu_grid failed");
  lean_object *a = lean_alloc_sarray(sizeof(double), 4, 4);
  double *d = lean_float_array_cptr(a);
  d[0] = r.minlo; d[1] = r.maxhi; d[2] = (double)r.fails; d[3] = ms;
  return lean_io_result_mk_ok(a);
}

LEAN_EXPORT lean_obj_res lean_ivgpu_list(uint32_t fn, b_lean_obj_arg boxes, lean_obj_arg w) {
  size_t n = lean_sarray_size(boxes) / 4;
  lean_object *a = lean_alloc_sarray(sizeof(double), 2 * n, 2 * n);
  if (fn > 1 || ivgpu_list((int)fn, lean_float_array_cptr(boxes), n, lean_float_array_cptr(a), 0)) {
    lean_dec(a); return io_err("ivgpu_list failed");
  }
  return lean_io_result_mk_ok(a);
}
