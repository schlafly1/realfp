/* Lean wrappers for the Interval128 kernels (c/interval128.h). */
#define _GNU_SOURCE
#include <lean/lean.h>
#include "interval128.h"

static inline i128_t i128_get(b_lean_obj_arg o) {
  return (i128_t){ lean_ctor_get_float(o, 0), lean_ctor_get_float(o, 8),
                   lean_ctor_get_float(o, 16), lean_ctor_get_float(o, 24) };
}
static inline lean_obj_res i128_box(i128_t r) {
  lean_object *o = lean_alloc_ctor(0, 0, 32);
  lean_ctor_set_float(o, 0, r.lh);
  lean_ctor_set_float(o, 8, r.ll);
  lean_ctor_set_float(o, 16, r.uh);
  lean_ctor_set_float(o, 24, r.ul);
  return o;
}

LEAN_EXPORT double i128_fma_down(double a, double b, double c) { return fma_dn(a, b, c); }
LEAN_EXPORT double i128_fma_up(double a, double b, double c) { return fma_up(a, b, c); }

LEAN_EXPORT lean_obj_res i128_add(b_lean_obj_arg x, b_lean_obj_arg y) { return i128_box(i128k_add(i128_get(x), i128_get(y))); }
LEAN_EXPORT lean_obj_res i128_sub(b_lean_obj_arg x, b_lean_obj_arg y) { return i128_box(i128k_sub(i128_get(x), i128_get(y))); }
LEAN_EXPORT lean_obj_res i128_mul(b_lean_obj_arg x, b_lean_obj_arg y) { return i128_box(i128k_mul(i128_get(x), i128_get(y))); }
LEAN_EXPORT lean_obj_res i128_div(b_lean_obj_arg x, b_lean_obj_arg y) { return i128_box(i128k_div(i128_get(x), i128_get(y))); }
LEAN_EXPORT lean_obj_res i128_sqrt(b_lean_obj_arg x) { return i128_box(i128k_sqrt(i128_get(x))); }

/* Backend id: 0 = AVX-512 embedded rounding, 1 = RN + exact error term. */
LEAN_EXPORT uint8_t i128_backend_id(lean_obj_arg u) { (void)u; return I128_AVX512 ? 0 : 1; }
