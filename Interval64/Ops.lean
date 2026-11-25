/-
More interval operations (all plain Lean over the directed scalar kernels and
`Float` comparisons; no new C code).

* `neg` (`-X`, exact), `abs`, `square` (dependency-aware: `square [-1, 2] = [0, 4]`
  whereas `X * X = [-2, 4]`), `pown X n` (natural power; dependency-aware for even
  `n`, monotone endpoint rule for odd `n`), `Interval64.min` / `Interval64.max`
  (pointwise), `inv` (`1 / X`; `whole` if `0 ∈ X`).
* `intersect` (may be empty: then `invalid`, i.e. `[NaN, NaN]`), `hull` (binary;
  an invalid argument is ignored).
* `mid` (a point of `X`; `0` for `whole`, finite for half-lines), `width` (`hi - lo`
  rounded up), `mag` (`max |x|`), `mig` (`min |x|`), `bisect` (two halves at `mid`).
* `subset X Y` (`X ⊆ Y`, false if either is invalid), `contains X f` (`f ∈ X`).

NaN policy as elsewhere: an invalid (NaN-endpoint) argument gives `invalid`
(NaN for the scalar-valued `mid`, `width`, `mag`, `mig`).
-/
import Interval64.Interval

namespace Interval64

open Interval64.Directed

/-- `-X = [-hi, -lo]` (exact). -/
protected def neg (a : Interval64) : Interval64 := ⟨-a.hi, -a.lo⟩

instance : Neg Interval64 := ⟨Interval64.neg⟩

/-- `|X|`: `X` if `0 ≤ lo`, `-X` if `hi ≤ 0`, else `[0, max (-lo) hi]` (exact). -/
protected def abs (a : Interval64) : Interval64 :=
  if a.lo.isNaN || a.hi.isNaN then invalid
  else if decide (0 ≤ a.lo) then a
  else if decide (a.hi ≤ 0) then ⟨-a.hi, -a.lo⟩
  else ⟨0, fmax (-a.lo) a.hi⟩

/-- `X²` with the dependency taken into account (result `⊆ [0, ∞]`). -/
def square (a : Interval64) : Interval64 :=
  if a.lo.isNaN || a.hi.isNaN then invalid
  else if decide (0 ≤ a.lo) then ⟨mulDown a.lo a.lo, mulUp a.hi a.hi⟩
  else if decide (a.hi ≤ 0) then ⟨mulDown a.hi a.hi, mulUp a.lo a.lo⟩
  else ⟨0, fmax (mulUp a.lo a.lo) (mulUp a.hi a.hi)⟩

/-- `acc * b ^ e` by binary exponentiation (interval `square` / `*`), `fuel` halvings
    (`whole` if the fuel runs out, which needs `e ≥ 2 ^ fuel`). -/
def ipowAux : Nat → Interval64 → Nat → Interval64 → Interval64
  | 0, _, e, acc => if e == 0 then acc else whole
  | fuel + 1, b, e, acc =>
    if e == 0 then acc
    else ipowAux fuel (square b) (e / 2) (if e % 2 == 1 then mul acc b else acc)

/-- Enclosure of `B ^ e` (binary exponentiation; used on point intervals). -/
def ipow (b : Interval64) (e : Nat) : Interval64 := ipowAux 64 b e ⟨1, 1⟩

/-- Lower bound of `f ^ n` (`f` itself if infinite). -/
def powLo (f : Float) (n : Nat) : Float := if f.isInf then f else (ipow ⟨f, f⟩ n).lo

/-- Upper bound of `f ^ n` (`f` itself if infinite). -/
def powHi (f : Float) (n : Nat) : Float := if f.isInf then f else (ipow ⟨f, f⟩ n).hi

/-- `X ^ n` for a natural `n`. `n = 0`: `[1, 1]`. Odd `n` (monotone):
    `[lo ^ n ↓, hi ^ n ↑]`. Even `n`: the same rule on `|X|` (so the result is `≥ 0`). -/
def pown (a : Interval64) (n : Nat) : Interval64 :=
  if a.lo.isNaN || a.hi.isNaN then invalid
  else if n == 0 then ⟨1, 1⟩
  else if n % 2 == 1 then ⟨powLo a.lo n, powHi a.hi n⟩
  else
    let b := Interval64.abs a
    ⟨powLo b.lo n, powHi b.hi n⟩

/-- Pointwise minimum `{min x y | x ∈ X, y ∈ Y}` (exact). -/
protected def min (a b : Interval64) : Interval64 :=
  if anyNan a b then invalid else ⟨fmin a.lo b.lo, fmin a.hi b.hi⟩

/-- Pointwise maximum (exact). -/
protected def max (a b : Interval64) : Interval64 :=
  if anyNan a b then invalid else ⟨fmax a.lo b.lo, fmax a.hi b.hi⟩

instance : Min Interval64 := ⟨Interval64.min⟩
instance : Max Interval64 := ⟨Interval64.max⟩

/-- `1 / X`; `whole` if `0 ∈ X` (so `x⁻¹ ∈ inv X` holds for every `x ∈ X`, with
    Lean's `0⁻¹ = 0`). -/
def inv (a : Interval64) : Interval64 :=
  if a.lo.isNaN || a.hi.isNaN then invalid
  else if containsZero a then whole
  else ⟨divDown 1 a.hi, divUp 1 a.lo⟩

/-- `X ∩ Y`. Empty intersections give `invalid` (`[NaN, NaN]`, the empty set). -/
def intersect (a b : Interval64) : Interval64 :=
  if anyNan a b then invalid
  else
    let lo := fmax a.lo b.lo
    let hi := fmin a.hi b.hi
    if decide (lo ≤ hi) then ⟨lo, hi⟩ else invalid

/-- Interval hull of `X ∪ Y`; an invalid argument is ignored. -/
def hull (a b : Interval64) : Interval64 :=
  if a.lo.isNaN || a.hi.isNaN then b
  else if b.lo.isNaN || b.hi.isNaN then a
  else ⟨fmin a.lo b.lo, fmax a.hi b.hi⟩

/-- Largest finite binary64. -/
def maxFloat : Float := Float.ofBits 0x7FEFFFFFFFFFFFFF

/-- `lo/2 + hi/2` with infinite ends replaced by `∓maxFloat` (round to nearest). -/
def midRaw (a : Interval64) : Float :=
  0.5 * fmax a.lo (-maxFloat) + 0.5 * fmin a.hi maxFloat

/-- A point of `X`: `midRaw X` clamped into `[lo, hi]` (so `whole ↦ 0` and half-lines give
    a finite point). NaN if `X` is invalid. -/
def mid (a : Interval64) : Float :=
  if a.lo.isNaN || a.hi.isNaN then Float.nan
  else fmin (fmax (midRaw a) a.lo) a.hi

/-- Width `hi - lo`, rounded up (an upper bound, used by search heuristics). The exact width is
`X.widthRat : Option Rat` (`Interval64.Display`). -/
def width (a : Interval64) : Float := subUp a.hi a.lo

/-- Magnitude `max {|x| : x ∈ X} = max (-lo) hi` (exact). -/
def mag (a : Interval64) : Float := fmax (-a.lo) a.hi

/-- Mignitude `min {|x| : x ∈ X}` (exact; `0` if `0 ∈ X`). -/
def mig (a : Interval64) : Float :=
  if a.lo.isNaN || a.hi.isNaN then Float.nan
  else if decide (0 ≤ a.lo) then a.lo
  else if decide (a.hi ≤ 0) then -a.hi
  else 0

/-- Split `X` at `mid X` into two intervals covering `X`. -/
def bisect (a : Interval64) : Interval64 × Interval64 :=
  let m := mid a
  (⟨a.lo, m⟩, ⟨m, a.hi⟩)

/-- `X ⊆ Y` (false if either is invalid). -/
def subset (a b : Interval64) : Bool :=
  !anyNan a b && decide (b.lo ≤ a.lo) && decide (a.hi ≤ b.hi)

/-- `f ∈ X` (false if `f` or an endpoint is NaN). -/
def contains (a : Interval64) (f : Float) : Bool :=
  decide (a.lo ≤ f) && decide (f ≤ a.hi)

end Interval64

namespace Interval64

/-- `X.hiLe q`: the upper endpoint of `X` is a finite double `≤ q`. Decidable by evaluation
(`decide +kernel`); with `RealFP.le_of_mem_hiLe` it turns `x ∈ X` into `x ≤ q`. -/
def hiLe (X : Interval64) (q : Rat) : Bool :=
  match Spec.bitsToRat? X.hi.toBits with
  | some h => decide (h ≤ q)
  | none => false

/-- `X.loGe q`: the lower endpoint of `X` is a finite double `≥ q` (see `RealFP.ge_of_mem_loGe`). -/
def loGe (X : Interval64) (q : Rat) : Bool :=
  match Spec.bitsToRat? X.lo.toBits with
  | some l => decide (q ≤ l)
  | none => false

end Interval64
