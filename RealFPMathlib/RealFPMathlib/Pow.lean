/-
`Real.rpow` enclosure (`Interval64.rpow`), and `∈`-style (`RealFP.Iv`) restatements of the
enclosure theorems for π, atan, atan2, sinh, cosh, tanh, log2, log10, tan, asin, acos, rpow.
-/
import RealFPMathlib.Conv
import RealFPMathlib.InvTrig
import RealFPMathlib.Hyp
import RealFPMathlib.Tan
import RealFPMathlib.Asin
import Interval64.Pow

open Interval64 Interval64.Spec

namespace RealFP.Pow

/-- `x ^ y ∈ rpow X Y` for every `x ∈ X` with `0 < x` and every `y ∈ Y`
    (no finiteness assumption on `X` or `Y`). -/
theorem rpow_mem_toSet {X Y : Interval64} {x y : ℝ} (hx : x ∈ X.toSet) (hy : y ∈ Y.toSet)
    (hx0 : 0 < x) : x ^ y ∈ (Interval64.rpow X Y).toSet := by
  rw [Real.rpow_def_of_pos hx0, mul_comm]
  exact Transc.exp_mem_toSet (mem_toSet_mul hy (Transc.log_mem_toSet hx hx0))

end RealFP.Pow

namespace RealFP.Iv

theorem pi_mem : Real.pi ∈ Interval64.pi := InvTrig.pi_mem_toSet

theorem atan_mem {X : Interval64} {x : ℝ} (hx : x ∈ X) : Real.arctan x ∈ Interval64.atan X :=
  InvTrig.atan_mem_toSet hx

theorem atan2_mem {X Y : Interval64} {x y : ℝ} (hx : x ∈ X) (hy : y ∈ Y) :
    Complex.arg ((x : ℂ) + (y : ℂ) * Complex.I) ∈ Interval64.atan2 Y X :=
  InvTrig.atan2_mem_toSet hx hy

theorem sinh_mem {X : Interval64} {x : ℝ} (hx : x ∈ X) : Real.sinh x ∈ Interval64.sinh X :=
  Hyp.sinh_mem_toSet hx

theorem cosh_mem {X : Interval64} {x : ℝ} (hx : x ∈ X) : Real.cosh x ∈ Interval64.cosh X :=
  Hyp.cosh_mem_toSet hx

theorem tanh_mem {X : Interval64} {x : ℝ} (hx : x ∈ X) : Real.tanh x ∈ Interval64.tanh X :=
  Hyp.tanh_mem_toSet hx

theorem log2_mem {X : Interval64} {x : ℝ} (hx : x ∈ X) (hx0 : 0 < x) :
    Real.logb 2 x ∈ Interval64.log2 X :=
  Hyp.log2_mem_toSet hx hx0

theorem log10_mem {X : Interval64} {x : ℝ} (hx : x ∈ X) (hx0 : 0 < x) :
    Real.logb 10 x ∈ Interval64.log10 X :=
  Hyp.log10_mem_toSet hx hx0

theorem tan_mem {X : Interval64} {x : ℝ} (hx : x ∈ X) : Real.tan x ∈ Interval64.tan X :=
  Tan.tan_mem_toSet hx

theorem asin_mem {X : Interval64} {x : ℝ} (hx : x ∈ X) : Real.arcsin x ∈ Interval64.asin X :=
  Asin.asin_mem_toSet hx

theorem acos_mem {X : Interval64} {x : ℝ} (hx : x ∈ X) : Real.arccos x ∈ Interval64.acos X :=
  Asin.acos_mem_toSet hx

theorem rpow_mem {X Y : Interval64} {x y : ℝ} (hx : x ∈ X) (hy : y ∈ Y) (hx0 : 0 < x) :
    x ^ y ∈ Interval64.rpow X Y :=
  Pow.rpow_mem_toSet hx hy hx0

end RealFP.Iv
