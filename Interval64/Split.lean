/-
Extended ("split") interval division, in the style of IEEE 1788 `mulRevToPair`.

`divSplit a b : Interval64Pair` encloses `{x / y | x ∈ a, y ∈ b, y ≠ 0}` as a
union of at most two intervals:

* `.empty`        : no reals;
* `.one I`        : `I`;
* `.two u l`      : `[-∞, u] ∪ [l, +∞]` (the complement of a gap `(u, l)`).

The existing `/` (`Interval64.div`) is unchanged; `divSplit` is built from the
same directed `divDown`/`divUp` kernels and the same Float comparisons, so it
is fast (at most 2 directed divisions in the split cases).

| `a`                | `b`                        | result                                   |
|--------------------|----------------------------|------------------------------------------|
| NaN endpoint       | any / NaN endpoint         | `.one invalid`                           |
| any                | `0 ∉ b`                    | `.one (a / b)` (as `/`)                  |
| any                | `[0, 0]`                   | `.empty`                                 |
| `0 ∈ a`            | `0 ∈ b`, `b ≠ [0, 0]`      | `.one whole`                             |
| `a > 0`            | `[0, d]`, `d > 0`          | `.one [a.lo / d ↓, +∞]`                  |
| `a > 0`            | `[c, 0]`, `c < 0`          | `.one [-∞, a.lo / c ↑]`                  |
| `a > 0`            | `c < 0 < d`                | `.two (a.lo / c ↑) (a.lo / d ↓)`          |
| `a < 0`            | `[0, d]`, `d > 0`          | `.one [-∞, a.hi / d ↑]`                  |
| `a < 0`            | `[c, 0]`, `c < 0`          | `.one [a.hi / c ↓, +∞]`                  |
| `a < 0`            | `c < 0 < d`                | `.two (a.hi / d ↑) (a.hi / c ↓)`          |

Example: `5 / [-2, 3] = [-∞, -5/2] ∪ [5/3, +∞]` (endpoints rounded outward).
`hull` (also the coercion `Interval64Pair → Interval64`) is `invalid` for
`.empty`, `I` for `.one I`, and `whole` for `.two`.
-/
import Interval64.Interval

namespace Interval64

open Interval64.Directed

/-- A union of at most two intervals (result of extended division). -/
inductive Interval64Pair where
  /-- No reals. -/
  | empty
  /-- One interval. -/
  | one (I : Interval64)
  /-- `[-∞, u] ∪ [l, +∞]`. -/
  | two (u l : Float)
  deriving Repr, Inhabited

namespace Interval64Pair

/-- First piece (`invalid`, i.e. no reals, if absent). -/
def piece1 : Interval64Pair → Interval64
  | .empty => invalid
  | .one I => I
  | .two u _ => ⟨-Float.inf, u⟩

/-- Second piece (`invalid`, i.e. no reals, if absent). -/
def piece2 : Interval64Pair → Interval64
  | .empty => invalid
  | .one _ => invalid
  | .two _ l => ⟨l, Float.inf⟩

/-- The pieces as a list (0, 1 or 2 intervals). -/
def toList : Interval64Pair → List Interval64
  | .empty => []
  | .one I => [I]
  | .two u l => [⟨-Float.inf, u⟩, ⟨l, Float.inf⟩]

/-- Interval hull: `invalid` (empty), the piece, or `whole` for two pieces. -/
def hull : Interval64Pair → Interval64
  | .empty => invalid
  | .one I => I
  | .two _ _ => whole

/-- Fold over the pieces (e.g. to process each half of a split box). -/
def foldl {α : Type} (f : α → Interval64 → α) (init : α) (P : Interval64Pair) : α :=
  P.toList.foldl f init

end Interval64Pair

instance : Coe Interval64Pair Interval64 := ⟨Interval64Pair.hull⟩

/-- Extended division (see the module docstring for the case table). -/
def divSplit (a b : Interval64) : Interval64Pair :=
  if anyNan a b then .one invalid
  else if !containsZero b then .one (div a b)
  else
    let bneg := !decide (0 ≤ b.lo)   -- b.lo < 0
    let bpos := !decide (b.hi ≤ 0)   -- 0 < b.hi
    if !bneg && !bpos then .empty
    else if containsZero a then .one whole
    else if !decide (a.lo ≤ 0) then            -- a > 0
      if !bneg then .one ⟨divDown a.lo b.hi, Float.inf⟩
      else if !bpos then .one ⟨-Float.inf, divUp a.lo b.lo⟩
      else .two (divUp a.lo b.lo) (divDown a.lo b.hi)
    else                                        -- a < 0
      if !bneg then .one ⟨-Float.inf, divUp a.hi b.hi⟩
      else if !bpos then .one ⟨divDown a.hi b.lo, Float.inf⟩
      else .two (divUp a.hi b.hi) (divDown a.hi b.lo)

end Interval64
