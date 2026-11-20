/-
Round-to-nearest + one-ulp outward widening. Sound if the hardware `+` / `*`
match IEEE RN (Lean’s `Float.Model` assumption), but slightly looser than
true directed rounding. Implemented in C so we do not depend on Lean’s
compiler to preserve the RN operation, then we apply `nextDown` / `nextUp`.
-/
namespace Interval64.Widen

@[extern "iv64_widen_add_down"] opaque addDown (a b : Float) : Float
@[extern "iv64_widen_add_up"]   opaque addUp   (a b : Float) : Float
@[extern "iv64_widen_sub_down"] opaque subDown (a b : Float) : Float
@[extern "iv64_widen_sub_up"]   opaque subUp   (a b : Float) : Float
@[extern "iv64_widen_mul_down"] opaque mulDown (a b : Float) : Float
@[extern "iv64_widen_mul_up"]   opaque mulUp   (a b : Float) : Float
@[extern "iv64_widen_div_down"] opaque divDown (a b : Float) : Float
@[extern "iv64_widen_div_up"]   opaque divUp   (a b : Float) : Float
@[extern "iv64_widen_sqrt_down"] opaque sqrtDown (a : Float) : Float
@[extern "iv64_widen_sqrt_up"]   opaque sqrtUp   (a : Float) : Float

end Interval64.Widen
