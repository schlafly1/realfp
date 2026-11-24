/-
Companion file for `TUTORIAL.md` (repository root). Every Lean snippet in the tutorial is here,
in the same order, and is checked by the default `lake build` (from `RealFPMathlib/`).
Outputs of `#eval`, `#realfp_min` and error messages are pinned with `#guard_msgs`, so the text
in the tutorial cannot drift from what the library really prints.

Everything uses only `propext`, `Classical.choice`, `Quot.sound`, except `RealFP.Examples.Tutorial.native_demo`
and `native_demo'`, which show `trust := native` (the axiom audit allows `native_decide` in
`RealFP.Examples.*` only).
-/
import RealFPMathlib.Front
import RealFPMathlib.KMatrix
import RealFPMathlib.KQuad
import Interval64.Kernel.QuadCert
import Interval128

open Interval64

namespace RealFP.Examples.Tutorial

/-! ## §1 Setup: is the C backend loaded and usable on this CPU? -/

/-- info: true -/
#guard_msgs in
#eval Interval64.Directed.backendOk ()

-- "avx512 (embedded rounding)" on x86-64, "rn+err (…)" on arm64 (not pinned: machine-dependent).
#guard_msgs (drop info) in
#eval Interval64.Directed.backendName

/-! ## §2 Computing with `Interval64` -/

-- Literals are *exact* decimals enclosed outward: `0.1` is two adjacent doubles.
/--
info: { lo := 0.100000, hi := 0.100000 }
-/
#guard_msgs in
#eval (0.1 : Interval64)
/--
info: some (7205759403792793 / 72057594037927936)
-/
#guard_msgs in
#eval Interval64.Spec.bitsToRat? (0.1 : Interval64).lo.toBits
/--
info: some (3602879701896397 / 36028797018963968)
-/
#guard_msgs in
#eval Interval64.Spec.bitsToRat? (0.1 : Interval64).hi.toBits

-- Arithmetic and elementary functions.
/--
info: { lo := 0.300000, hi := 0.300000 }
-/
#guard_msgs in
#eval (0.1 : Interval64) + 0.2
/--
info: { lo := 1.414214, hi := 1.414214 }
-/
#guard_msgs in
#eval Interval64.sqrt 2
/--
info: { lo := 2.718282, hi := 2.718282 }
-/
#guard_msgs in
#eval Interval64.exp 1
/--
info: { lo := 3.141593, hi := 3.141593 }
-/
#guard_msgs in
#eval Interval64.pi
/--
info: { lo := 0.841471, hi := 1.000000 }
-/
#guard_msgs in
#eval Interval64.sin (ofRatInterval 1 2)

-- Dependency: `X * X - X` on `[0, 1]` is `[-1, 1]`, not the true range `[-1/4, 0]`.
/--
info: { lo := -1.000000, hi := 1.000000 }
-/
#guard_msgs in
#eval ofRatInterval 0 1 * ofRatInterval 0 1 - ofRatInterval 0 1

-- Edge cases: empty (NaN) and whole-line results.
/--
info: { lo := NaN, hi := NaN }
-/
#guard_msgs in
#eval Interval64.sqrt (-1)
/--
info: { lo := -inf, hi := inf }
-/
#guard_msgs in
#eval (1 : Interval64) / ofRatInterval (-1) 1

-- Interval128: double-double endpoints, ~106 bits.
/--
info: { lo := 1.414214, hi := 1.414214 }
-/
#guard_msgs in
open Interval128 in
#eval (Interval128.sqrt 2).toInterval64
-- Widths of `√2`: one ulp (2⁻⁵²) for Interval64, about 2⁻¹⁰⁵ for Interval128.
/--
info: some (1 / 4503599627370496)
-/
#guard_msgs in
#eval Interval64.Spec.bitsToRat? (Interval64.width (Interval64.sqrt 2)).toBits
/--
info: some (1 / 40564819207303340847894502572032)
-/
#guard_msgs in
open Interval128 in
#eval Interval64.Spec.bitsToRat? (Interval128.sqrt 2).width.toBits

/-! ## §3 First proofs with `realfp` -/

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sin x ≤ x + 1/1000 := by realfp
example (x : ℝ) (h₀ : 1 ≤ x) (h₁ : x ≤ 2) : Real.exp x < 8 := by realfp
example : (1.414 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 1.4143 := by realfp
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, x * y - x - y ≥ -1.01 := by realfp
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≠ 2 * x := by realfp

-- Touching bounds (equality at a point) work thanks to derivative certificates.
example : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 1 + x ≤ Real.exp x := by realfp

-- Failure messages
/--
error: realfp (trust := kernel): routed to `interval`: interval: no certificate within depth 24 / 50000 boxes (1589 evaluations): the bound is false: the maximum is ≈ 0.367879441171 at x✝ ≈ 1 (rigorous value at that point), beyond 0.3678
-/
#guard_msgs in
example : ∀ x ∈ Set.Icc (0 : ℝ) 4, x * Real.exp (-x) ≤ 0.3678 := by realfp

-- Options
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sin x ≤ x + 1/1000 := by
  realfp (depth := 30) (maxBoxes := 100000) (chunk := 16)
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * (1 - x) ≤ 1/4 + 1/100 := by realfp (deriv := false)

/-! ## §4 Trust -/

theorem sin_le : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sin x ≤ x + 1/1000 := by realfp

/--
info: 'RealFP.Examples.Tutorial.sin_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sin_le

theorem native_demo : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sin x ≤ x + 1/1000 := by
  realfp (trust := native)

/--
info: 'RealFP.Examples.Tutorial.native_demo' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 native_demo._native.native_decide.ax_1_7]
-/
#guard_msgs in
#print axioms native_demo

set_option realfp.native true in
theorem native_demo' : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.cos x ≥ 1/2 := by realfp

/-! ## §5 Tactics in depth -/

-- interval directly
example (x : ℝ) (h0 : 2 ≤ x) (h1 : x ≤ 3) : Real.log x ∈ Set.Icc (0.69 : ℝ) 1.1 := by interval

-- integrals
example : (0.7468 : ℝ) ≤ ∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2) := by realfp
example : (∫ x in (1 : ℝ)..2, 1 / x) ∈ Set.Icc (0.6931 : ℝ) 0.6932 := by integral_bound

-- roots
example : ∃! x ∈ Set.Icc (1 : ℝ) 2, x ^ 2 = 2 := by realfp
example : ∃ x ∈ Set.Icc (0 : ℝ) 1, Real.cos x = x := by root_exists
example : ∃! x ∈ Set.Icc (0 : ℝ) 1, Real.cos x = x := by root_unique
example : ∃ x ∈ Set.Icc (1.3247 : ℝ) 1.3248, x ^ 3 - x - 1 = 0 := by realfp
example : ∃! p : ℝ × ℝ, p.1 ∈ Set.Icc (0.9 : ℝ) 1.1 ∧ p.2 ∈ Set.Icc (0.9 : ℝ) 1.1 ∧
    p.1 ^ 2 + p.2 = 2 ∧ p.1 + p.2 ^ 2 = 2 := by realfp
example : ∃ p : ℝ × ℝ, p.1 ∈ Set.Icc (0 : ℝ) 3 ∧ p.2 ∈ Set.Icc (0 : ℝ) 3 ∧
    p.1 ^ 2 + p.2 ^ 2 = 4 ∧ p.1 = p.2 := by realfp

-- wide box, unique: fails
/--
error: realfp (trust := kernel): routed to `root_unique`: root_unique: no certificate for the system on [0, 3] × [0, 3]:
• Krawczyk on the whole box [0, 3] × [0, 3]: centre = midpoint: contraction factor ‖I - Y·J(X)‖∞ ≈ 1.000000 ≥ 1 (box too wide or Jacobian too ill-conditioned); centre = Newton point: contraction factor ‖I - Y·J(X)‖∞ ≈ 1.121320 ≥ 1 (box too wide or Jacobian too ill-conditioned)
 An approximate root is (1.414214, 1.414214); a smaller box around it usually works for `∃!`.
-/
#guard_msgs in
example : ∃! p : ℝ × ℝ, p.1 ∈ Set.Icc (0 : ℝ) 3 ∧ p.2 ∈ Set.Icc (0 : ℝ) 3 ∧
    p.1 ^ 2 + p.2 ^ 2 = 4 ∧ p.1 = p.2 := by realfp

-- PD
example : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by realfp
example : (!![4, 1, 0; 1, 3, 1; 0, 1, 2] : Matrix (Fin 3) (Fin 3) ℝ).PosDef := by pos_def

-- optimisation
/--
info: minimum ∈ [-0.232465575843, -0.232465575159] (gap 0.000000000683762102494, 77 boxes; estimate from the enclosures, not a proof)
attained near x ≈ -0.450183611364
statements `realfp` should prove:
  ∀ x ∈ Set.Icc (-1 : ℝ) 1, -0.232467 ≤ x ^ 2 + Real.sin x
  ∃ x ∈ Set.Icc (-1 : ℝ) 1, x ^ 2 + Real.sin x ≤ -0.232464
-/
#guard_msgs in
#realfp_min (x ∈ Set.Icc (-1:ℝ) 1), x ^ 2 + Real.sin x

example : ∀ x ∈ Set.Icc (-1 : ℝ) 1, -0.232467 ≤ x ^ 2 + Real.sin x := by realfp
example : ∃ x ∈ Set.Icc (-1 : ℝ) 1, x ^ 2 + Real.sin x ≤ -0.232464 := by realfp
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x ^ 2 - x ≥ -1/4 := by realfp
example : ∃ m : ℚ, ∀ x ∈ Set.Icc (0 : ℝ) 1, x ^ 2 + Real.sin x ≥ m := by realfp
example : sInf ((fun x : ℝ => x ^ 2 - x) '' Set.Icc 0 1) = -1/4 := by realfp
example : |sInf ((fun x : ℝ => x ^ 2 + Real.sin x) '' Set.Icc (-1) 1) - (-0.2324656)| ≤ 1/10^6 := by
  realfp
example : ∃ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, x ^ 2 - x ≤ y ^ 2 - y := by realfp
example : ∃ x ∈ Set.Icc (-0.451 : ℝ) (-0.45), ∀ y ∈ Set.Icc (-1 : ℝ) 1,
    x ^ 2 + Real.sin x ≤ y ^ 2 + Real.sin y := by realfp
example : ∀ x ∈ Set.Icc (-5 : ℝ) 5, ∀ y ∈ Set.Icc (-5 : ℝ) 5,
    (x^2 + y - 11)^2 + (x + y^2 - 7)^2 ≥ -1/100 := by realfp

/-! ## §6 Lower level -/

section Manual
open Interval64.Spec

/-- `[1/10, 3/10]`, rounded outward. -/
def I : Interval64 := ofRatInterval (1/10) (3/10)
/-- One interval evaluation of `x * x + x`. -/
def J : Interval64 := I * I + I

theorem J_hi_le : J.hi ≤ 0.40625 := by decide +kernel

theorem sq_add_le (x : ℝ) (hx : x ∈ Set.Icc (1/10 : ℝ) (3/10)) : x * x + x ≤ 13/32 := by
  have hxI : x ∈ I :=
    mem_toSet_ofRatInterval (by push_cast; linarith [hx.1]) (by push_cast; linarith [hx.2])
  have hJ : x * x + x ∈ J := Iv.add_mem (Iv.mem_mul hxI hxI) hxI
  have h := le_of_mem_toSet_of_hi_le (q := 13/32) hJ J_hi_le (by decide +kernel)
  push_cast at h
  linarith

end Manual

-- Kernel-path certificates without a tactic: a 4×4 Hilbert matrix is positive definite.
def hq (i j : ℕ) : ℚ := 1 / ((i : ℚ) + j + 1)
def H4 : Array Interval64.KF.KI := ki_lit% (Interval64.KF.KM.ofRatFn 4 hq)

theorem hilbert4_posDef : (Matrix.of fun i j : Fin 4 => ((hq i j : ℚ) : ℝ)).PosDef :=
  RealFP.KM.posDef_of_ratMat (A := H4) (c := pd_certs% 4 H4) (by decide +kernel)
    (by decide +kernel) (fun i j _ _ => by simp [hq, add_comm])

-- Taylor quadrature by hand: the integrand as a reflected expression `IExpr`.
open Interval64.KF in
def g : IExpr := .exp (.neg (.mul (.var 0) (.var 0)))

open Interval64.KF Interval64.KF.KQ RealFP.KQ in
theorem gauss_bounds :
    (7468 / 10000 : ℝ) ≤ ∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2) ∧
      (∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) ≤ 7469 / 10000 := by
  have h := integral_bounds_of_quadBound (e := g) (K := 4) (a := bits% 0) (b := bits% 1)
    (cs := cells% 0 1 4) (qa := 0) (qb := 1) (ql := 7468 / 10000) (qh := 7469 / 10000)
    (by decide +kernel)
  have e : ∀ x : ℝ, g.denote [x] = Real.exp (-x ^ 2) := fun x => by simp [g, IExpr.denote, sq]
  simp only [e] at h
  push_cast at h
  exact h

-- Splitting a check across declarations
theorem piece₁ : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x - 2 * x ≥ 0.6 := by realfp
theorem piece₂ : ∀ x ∈ Set.Icc (1 : ℝ) 2, Real.exp x - 2 * x ≥ 0.6 := by realfp

theorem glued : ∀ x ∈ Set.Icc (0 : ℝ) 2, Real.exp x - 2 * x ≥ 0.6 := by
  intro x ⟨h0, h2⟩
  rcases le_total x 1 with h | h
  · exact piece₁ x ⟨h0, h⟩
  · exact piece₂ x ⟨h, h2⟩

end RealFP.Examples.Tutorial
