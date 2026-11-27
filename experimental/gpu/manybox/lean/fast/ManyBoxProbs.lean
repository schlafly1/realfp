import Interval64

/-! The manybox v2 problems as `IExpr`s (Mathlib-free), in exactly the operation order of
`../../v2/mb2.h`. All on `[-1,1]^d`. -/

open Interval64.KF

namespace ManyBox.V2

def sqv (i : Nat) : IExpr := .pow (.var i) 2
/-- `T4(x) = (8u - 8)u + 1`, `u = x^2`. -/
def t4 (i : Nat) : IExpr := .add (.mul (.sub (.mul (.rat 8) (sqv i)) (.rat 8)) (sqv i)) (.rat 1)
/-- `T8(x) = (((128u - 256)u + 160)u - 32)u + 1`, `u = x^2`. -/
def t8 (i : Nat) : IExpr :=
  .add (.mul (.sub (.mul (.add (.mul (.sub (.mul (.rat 128) (sqv i)) (.rat 256)) (sqv i)) (.rat 160))
    (sqv i)) (.rat 32)) (sqv i)) (.rat 1)
/-- `2 + x_i ∈ [1, 3]`. -/
def sh (i : Nat) : IExpr := .add (.rat 2) (.var i)

/-- Nesbitt: `a/(b+c) + b/(c+a) + c/(a+b) ≥ 3/2` with `a = 2 + x` etc. (division). -/
def eNES : IExpr :=
  .add (.add (.div (sh 0) (.add (sh 1) (sh 2))) (.div (sh 1) (.add (sh 2) (sh 0)))) (.div (sh 2) (.add (sh 0) (sh 1)))

/-- Power means: `√a + √b + √c − √(3(a+b+c)) ≤ 0` (square roots). -/
def ePM : IExpr :=
  .sub (.add (.add (.sqrt (sh 0)) (.sqrt (sh 1))) (.sqrt (sh 2)))
    (.sqrt (.mul (.rat 3) (.add (.add (sh 0) (sh 1)) (sh 2))))

/-- Reznick's AM–GM (Motzkin-type) form in 6 variables:
    `x₆¹² + P (x₁² + ⋯ + x₅²) − 6 x₆² P ≥ 0`, `P = x₁² ⋯ x₅²`. -/
def eM6 : IExpr :=
  let P := .mul (.mul (.mul (.mul (sqv 0) (sqv 1)) (sqv 2)) (sqv 3)) (sqv 4)
  let S := .add (.add (.add (.add (sqv 0) (sqv 1)) (sqv 2)) (sqv 3)) (sqv 4)
  .sub (.add (.pow (.var 5) 12) (.mul P S)) (.mul (.mul (.rat 6) (sqv 5)) P)

/-- Ring of 8 Chebyshev "spins": `∑ᵢ T4(xᵢ) T4(xᵢ₊₁ mod 8) ≥ −8`. -/
def eR8 : IExpr :=
  (List.range 7).foldl (fun s i => .add s (.mul (t4 (i + 1)) (t4 ((i + 2) % 8)))) (.mul (t4 0) (t4 1))

/-- `∑ᵢ T8(xᵢ) ≤ 6` in 6 variables. -/
def eC6 : IExpr := (List.range 5).foldl (fun s i => .add s (t8 (i + 1))) (t8 0)

def cube (d : Nat) : List (Rat × Rat) := List.replicate d (-1, 1)

end ManyBox.V2
