/-
Directed fused multiply-add for binary64: `fmaDown a b c = RD(a*b + c)`,
`fmaUp a b c = RU(a*b + c)` with a single rounding (IEEE 754-2019 §5.4.1).

The specification reuses Interval64's software directed rounding: for finite
`a`, `b` the exact product `(s₁s₂, m₁m₂, e₁+e₂)` is added to `c` exactly by
`addU` (one rounding at the end). Zero `c` reduces to the rounded product
(`mulU`); every other operand pattern (zero / ∞ / NaN factor) goes through the
exact special-value product `mulU` followed by `addU`, which is IEEE's rule.

Runtime: `i128_fma_down` / `i128_fma_up` (AVX-512 embedded-rounding FMA on x86_64;
fesetround + `fma` elsewhere). Differentially tested against this spec.
-/
import Interval64

namespace Interval64.Spec

open Float.Model
open Float.Model.UnpackedFloat

def fmaU (x y z : UnpackedFloat) (up : Bool) : UnpackedFloat :=
  match x, y with
  | .finite s₁ m₁ e₁ h₁, .finite s₂ m₂ e₂ h₂ =>
    match z with
    | .zero _ => mulU (.finite s₁ m₁ e₁ h₁) (.finite s₂ m₂ e₂ h₂) up
    | z => addU (.finite (s₁ * s₂) (m₁ * m₂) (e₁ + e₂) (Nat.mul_pos h₁ h₂)) z up
  | x, y => addU (mulU x y up) z up

def fma (a b c : UInt64) (up : Bool) : UInt64 :=
  packDirected up (fmaU (unpackBits a) (unpackBits b) (unpackBits c) up)

def fmaDown (a b c : UInt64) : UInt64 := fma a b c false
def fmaUp   (a b c : UInt64) : UInt64 := fma a b c true

end Interval64.Spec

namespace Interval64.Directed

def fmaDownSpec (a b c : Float) : Float :=
  Float.ofBits (Spec.fmaDown a.toBits b.toBits c.toBits)
def fmaUpSpec (a b c : Float) : Float :=
  Float.ofBits (Spec.fmaUp a.toBits b.toBits c.toBits)

@[extern "i128_fma_down"] opaque fmaDownImpl (a b c : Float) : Float
@[extern "i128_fma_up"]   opaque fmaUpImpl   (a b c : Float) : Float

/-- `RD(a*b + c)`, one rounding. -/
@[implemented_by fmaDownImpl]
def fmaDown (a b c : Float) : Float := fmaDownSpec a b c
/-- `RU(a*b + c)`, one rounding. -/
@[implemented_by fmaUpImpl]
def fmaUp (a b c : Float) : Float := fmaUpSpec a b c

end Interval64.Directed
