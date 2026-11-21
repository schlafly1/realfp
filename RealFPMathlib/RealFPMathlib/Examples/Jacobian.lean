/-
Example 2: a polynomial map `F : ℝ³ → ℝ³` with constant Jacobian determinant
`-2` that is not injective.

  F(x,y,z) = ( (1+xy)³ z + y² (1+xy)(4+3xy),
               y + 3x (1+xy)² z + 3x y² (4+3xy),
               2x - 3x² y - x³ z )

* `hasDerivAt_*`: the nine partial derivatives, computed with Mathlib
  (`HasDerivAt`); `jac_det`: their determinant is `-2` everywhere.
* `F_eq_iff`: for `a ≠ 0`, `F(x,y,z) = (a,0,0)` iff
  `(x,y,z) = (0,0,a)` or (`x ≠ 0`, `4 a x² = -1`, `xy = -3/2`, `x² z = 13/2`).
  Proof: `F₃ = x (2 - 3xy - x²z)`; if `x ≠ 0`, eliminating `z` from
  `x · F₂ = 0` leaves `4xy + 6 = 0`, and then `x² F₁ = -1/4`.
* `solutions_quarter`: exactly 3 solutions of `F = (-1/4, 0, 0)`.
* `solutions_026`: exactly 3 solutions of `F = (-0.26, 0, 0)`:
  `(0, 0, -0.26)` and `(±s, ∓3/(2s), 169/25)` with `s = √(25/26)`.
  `s_mem`, `y_mem` give Interval64 enclosures of `s` and `-3/(2s)`
  (certified with `native_decide`), and `s_bounds`, `y_bounds` 10-digit bounds.
-/
import RealFPMathlib.Demo
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Set.Card
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

open Interval64 Interval64.Spec

namespace RealFP.Examples.Jacobian

def F1 (x y z : ℝ) : ℝ := (1 + x*y)^3 * z + y^2 * (1 + x*y) * (4 + 3*x*y)
def F2 (x y z : ℝ) : ℝ := y + 3*x*(1 + x*y)^2 * z + 3*x*y^2 * (4 + 3*x*y)
def F3 (x y z : ℝ) : ℝ := 2*x - 3*x^2*y - x^3*z

def F (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := (F1 p.1 p.2.1 p.2.2, F2 p.1 p.2.1 p.2.2, F3 p.1 p.2.1 p.2.2)

/-! ### The three points of the user's claim -/

theorem F_points :
    F (0, 0, -1/4) = (-1/4, 0, 0) ∧ F (1, -3/2, 13/2) = (-1/4, 0, 0) ∧
      F (-1, 3/2, 13/2) = (-1/4, 0, 0) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [F, F1, F2, F3, Prod.mk.injEq] <;> norm_num

/-! ### Partial derivatives (Mathlib) and the Jacobian determinant -/

theorem deriv_hmul (c x : ℝ) : deriv (HMul.hMul c) x = c := by
  have := ((hasDerivAt_id x).const_mul c).deriv
  rw [mul_one] at this; exact this

/-- Differentiate a polynomial in one variable: `HasDerivAt` via `deriv` + `ring`. -/
macro "pderiv" : tactic => `(tactic| (
  refine HasDerivAt.congr_deriv (DifferentiableAt.hasDerivAt ?_) ?_
  · fun_prop
  · simp (disch := fun_prop) only [deriv_fun_add, deriv_fun_sub, deriv_fun_mul, deriv_fun_pow,
      deriv_const, deriv_id'', deriv_hmul]
    ring))

def J11 (x y z : ℝ) : ℝ := 3*x^2*y^3*z + 6*x*y^4 + 6*x*y^2*z + 7*y^3 + 3*y*z
def J12 (x y z : ℝ) : ℝ := 3*x^3*y^2*z + 12*x^2*y^3 + 6*x^2*y*z + 21*x*y^2 + 3*x*z + 8*y
def J13 (x y _z : ℝ) : ℝ := x^3*y^3 + 3*x^2*y^2 + 3*x*y + 1
def J21 (x y z : ℝ) : ℝ := 9*x^2*y^2*z + 18*x*y^3 + 12*x*y*z + 12*y^2 + 3*z
def J22 (x y z : ℝ) : ℝ := 6*x^3*y*z + 27*x^2*y^2 + 6*x^2*z + 24*x*y + 1
def J23 (x y _z : ℝ) : ℝ := 3*x^3*y^2 + 6*x^2*y + 3*x
def J31 (x y z : ℝ) : ℝ := -3*x^2*z - 6*x*y + 2
def J32 (x _y _z : ℝ) : ℝ := -3*x^2
def J33 (x _y _z : ℝ) : ℝ := -x^3

theorem hasDerivAt_F1_x (x y z : ℝ) : HasDerivAt (fun t => F1 t y z) (J11 x y z) x := by
  unfold F1 J11; pderiv
theorem hasDerivAt_F1_y (x y z : ℝ) : HasDerivAt (fun t => F1 x t z) (J12 x y z) y := by
  unfold F1 J12; pderiv
theorem hasDerivAt_F1_z (x y z : ℝ) : HasDerivAt (fun t => F1 x y t) (J13 x y z) z := by
  unfold F1 J13; pderiv
theorem hasDerivAt_F2_x (x y z : ℝ) : HasDerivAt (fun t => F2 t y z) (J21 x y z) x := by
  unfold F2 J21; pderiv
theorem hasDerivAt_F2_y (x y z : ℝ) : HasDerivAt (fun t => F2 x t z) (J22 x y z) y := by
  unfold F2 J22; pderiv
theorem hasDerivAt_F2_z (x y z : ℝ) : HasDerivAt (fun t => F2 x y t) (J23 x y z) z := by
  unfold F2 J23; pderiv
theorem hasDerivAt_F3_x (x y z : ℝ) : HasDerivAt (fun t => F3 t y z) (J31 x y z) x := by
  unfold F3 J31; pderiv
theorem hasDerivAt_F3_y (x y z : ℝ) : HasDerivAt (fun t => F3 x t z) (J32 x y z) y := by
  unfold F3 J32; pderiv
theorem hasDerivAt_F3_z (x y z : ℝ) : HasDerivAt (fun t => F3 x y t) (J33 x y z) z := by
  unfold F3 J33; pderiv

/-- The Jacobian matrix of `F` (entries are the partial derivatives above). -/
def jac (x y z : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![J11 x y z, J12 x y z, J13 x y z;
     J21 x y z, J22 x y z, J23 x y z;
     J31 x y z, J32 x y z, J33 x y z]

/-- The Jacobian determinant is the constant `-2`. -/
theorem jac_det (x y z : ℝ) : (jac x y z).det = -2 := by
  simp only [jac, Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const,
    J11, J12, J13, J21, J22, J23, J31, J32, J33]
  ring

/-- `F` is not injective although its Jacobian determinant never vanishes. -/
theorem F_not_injective : ¬ Function.Injective F := fun h => by
  have := h (F_points.1.trans F_points.2.1.symm)
  simp at this

/-! ### Solving `F = (a, 0, 0)` -/

theorem F_eq_iff {a : ℝ} (ha : a ≠ 0) (x y z : ℝ) :
    F (x, y, z) = (a, 0, 0) ↔
      (x = 0 ∧ y = 0 ∧ z = a) ∨ (x ≠ 0 ∧ 4 * a * x ^ 2 = -1 ∧ x * y = -3/2 ∧ x ^ 2 * z = 13/2) := by
  simp only [F, F1, F2, F3, Prod.mk.injEq]
  constructor
  · rintro ⟨e1, e2, e3⟩
    by_cases hx : x = 0
    · subst hx
      left
      have hy : y = 0 := by linear_combination e2
      subst hy
      exact ⟨rfl, rfl, by linear_combination e1⟩
    · right
      have E3 : 2 - 3 * (x * y) - x ^ 2 * z = 0 := by
        have : x * (2 - 3 * (x * y) - x ^ 2 * z) = 0 := by linear_combination e3
        exact (mul_eq_zero.1 this).resolve_left hx
      have hw : x * y = -3/2 := by
        linear_combination (x * e2 + 3 * (1 + x * y) ^ 2 * E3) / 4
      have hz : x ^ 2 * z = 13/2 := by linear_combination -E3 - 3 * hw
      refine ⟨hx, ?_, hw, hz⟩
      have : x ^ 2 * ((1 + x*y)^3 * z + y^2 * (1 + x*y) * (4 + 3*x*y)) =
          (1 + x*y)^3 * (x^2 * z) + (x*y)^2 * (1 + x*y) * (4 + 3*(x*y)) := by ring
      rw [e1, hw, hz] at this
      linear_combination 4 * this
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨hx, h4, hw, hz⟩)
    · norm_num
    · have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
      refine ⟨?_, ?_, ?_⟩
      · have : x ^ 2 * ((1 + x*y)^3 * z + y^2 * (1 + x*y) * (4 + 3*x*y)) = x ^ 2 * a := by
          have e : x ^ 2 * ((1 + x*y)^3 * z + y^2 * (1 + x*y) * (4 + 3*x*y)) =
              (1 + x*y)^3 * (x^2 * z) + (x*y)^2 * (1 + x*y) * (4 + 3*(x*y)) := by ring
          rw [e, hw, hz]; linear_combination -h4 / 4
        exact mul_left_cancel₀ hx2 this
      · have : x * (y + 3*x*(1 + x*y)^2 * z + 3*x*y^2 * (4 + 3*x*y)) = x * 0 := by
          have e : x * (y + 3*x*(1 + x*y)^2 * z + 3*x*y^2 * (4 + 3*x*y)) =
              x*y + 3*(1 + x*y)^2 * (x^2 * z) + 3*(x*y)^2 * (4 + 3*(x*y)) := by ring
          rw [e, hw, hz]; norm_num
        exact mul_left_cancel₀ hx this
      · have e : 2*x - 3*x^2*y - x^3*z = x * (2 - 3 * (x*y) - x^2*z) := by ring
        rw [e, hw, hz]; norm_num

/-! ### `a = -1/4`: exactly three solutions -/

theorem solutions_quarter :
    {p : ℝ × ℝ × ℝ | F p = (-1/4, 0, 0)} = {(0, 0, -1/4), (1, -3/2, 13/2), (-1, 3/2, 13/2)} := by
  ext ⟨x, y, z⟩
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  rw [F_eq_iff (by norm_num)]
  constructor
  · rintro (h | ⟨hx, h4, hw, hz⟩)
    · exact Or.inl h
    · have hx1 : x ^ 2 = 1 := by linear_combination -h4
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hx1.trans (one_pow 2).symm) with h1 | h1 <;> subst h1
      · right; left; exact ⟨rfl, by linarith, by linarith⟩
      · right; right; exact ⟨rfl, by linarith, by linarith⟩
  · rintro (h | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · exact Or.inl h
    all_goals right; norm_num

theorem ncard_solutions_quarter : {p : ℝ × ℝ × ℝ | F p = (-1/4, 0, 0)}.ncard = 3 := by
  rw [solutions_quarter, Set.ncard_eq_three]
  exact ⟨_, _, _, by norm_num, by norm_num, by norm_num, rfl⟩

/-! ### `a = -0.26`: exactly three solutions, two irrational -/

/-- `s = √(25/26) = 5/√26`. -/
noncomputable def s : ℝ := Real.sqrt (25/26)

theorem s_pos : 0 < s := Real.sqrt_pos.2 (by norm_num)
theorem s_sq : s ^ 2 = 25/26 := Real.sq_sqrt (by norm_num)

theorem solutions_026 :
    {p : ℝ × ℝ × ℝ | F p = (-0.26, 0, 0)} =
      {(0, 0, -0.26), (s, -3 / (2 * s), 169/25), (-s, 3 / (2 * s), 169/25)} := by
  have hs := s_pos; have hs2 := s_sq
  ext ⟨x, y, z⟩
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  rw [F_eq_iff (by norm_num)]
  constructor
  · rintro (h | ⟨hx, h4, hw, hz⟩)
    · exact Or.inl h
    · have hx2 : x ^ 2 = s ^ 2 := by rw [hs2]; linear_combination -(25/26) * h4
      have hy : y = -3 / (2 * x) := by field_simp; linear_combination 2 * hw
      have hz' : z = 169/25 := by
        have : x ^ 2 * z = x ^ 2 * (169/25) := by rw [hz, hx2, hs2]; norm_num
        exact mul_left_cancel₀ (pow_ne_zero 2 hx) this
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hx2 with h1 | h1 <;> subst h1
      · right; left; exact ⟨rfl, hy, hz'⟩
      · right; right; refine ⟨rfl, by rw [hy]; field_simp, hz'⟩
  · rintro (h | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · exact Or.inl h
    · right
      refine ⟨hs.ne', by rw [hs2]; norm_num, by field_simp, by rw [hs2]; norm_num⟩
    · right
      refine ⟨neg_ne_zero.2 hs.ne', by rw [neg_sq, hs2]; norm_num, by field_simp,
        by rw [neg_sq, hs2]; norm_num⟩

theorem ncard_solutions_026 : {p : ℝ × ℝ × ℝ | F p = (-0.26, 0, 0)}.ncard = 3 := by
  have hs := s_pos
  rw [solutions_026, Set.ncard_eq_three]
  refine ⟨_, _, _, ?_, ?_, ?_, rfl⟩ <;> simp only [ne_eq, Prod.mk.injEq, not_and]
  · intro h; exact absurd h.symm hs.ne'
  · intro h; linarith
  · intro h; linarith

/-! ### Interval64 enclosures of the irrational coordinates -/

/-- Interval for `s = √(25/26)`. -/
def S : Interval64 := Interval64.sqrt (ofRat (25/26))
/-- Interval for `-3/(2s) = (-3/2)/s`. -/
def Y : Interval64 := ofRat (-3/2) / S

theorem S_lo : bitsToRat? S.lo.toBits = some (4416142765648337 / 4503599627370496) := by
  native_decide
theorem S_hi : bitsToRat? S.hi.toBits = some (8832285531296675 / 9007199254740992) := by
  native_decide
theorem Y_lo : bitsToRat? Y.lo.toBits = some (-6889182714411407 / 4503599627370496) := by
  native_decide
theorem Y_hi : bitsToRat? Y.hi.toBits = some (-6889182714411405 / 4503599627370496) := by
  native_decide

theorem s_mem : s ∈ S.toSet := by
  have h : (((25/26 : ℚ)) : ℝ) ∈ (ofRat (25/26)).toSet := mem_toSet_ofRat _
  have := sqrt_mem_toSet h (by norm_num)
    (Option.isSome_iff_exists.mp (by decide +kernel))
    (Option.isSome_iff_exists.mp (by decide +kernel))
  have e : (((25/26 : ℚ)) : ℝ) = 25/26 := by norm_num
  rw [e] at this
  exact this

theorem y_mem : -3 / (2 * s) ∈ Y.toSet := by
  have h : (((-3/2 : ℚ)) : ℝ) ∈ (ofRat (-3/2)).toSet := mem_toSet_ofRat _
  have := div_mem_toSet h s_mem s_pos.ne'
    (Option.isSome_iff_exists.mp (by decide +kernel))
    (Option.isSome_iff_exists.mp (by decide +kernel)) ⟨_, S_lo⟩ ⟨_, S_hi⟩
  have e : -3 / (2 * s) = (((-3/2 : ℚ)) : ℝ) / s := by push_cast; field_simp
  rw [e]; exact this

theorem s_bounds : (0.9805806756 : ℝ) < s ∧ s < 0.9805806757 := by
  have h := s_mem
  rw [toSet_eq_Icc S_lo S_hi] at h
  obtain ⟨h1, h2⟩ := h
  push_cast at h1 h2
  constructor <;> linarith

theorem y_bounds : (-1.5297058541 : ℝ) < -3 / (2 * s) ∧ -3 / (2 * s) < -1.5297058540 := by
  have h := y_mem
  rw [toSet_eq_Icc Y_lo Y_hi] at h
  obtain ⟨h1, h2⟩ := h
  push_cast at h1 h2
  constructor <;> linarith

end RealFP.Examples.Jacobian
