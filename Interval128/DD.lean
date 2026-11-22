/-
Double-double endpoint kernels for `Interval128`.

A double-double `(hi, lo)` stands for the exact real `hi + lo`. Each kernel
returns a pair whose exact sum is a rigorous lower (`*Lo`) or upper (`*Hi`)
bound of the exact result, *whenever both returned words are finite*.

Method. Approximations (`s`, `q₁`, `q₂`, ...) are computed in ordinary
round-to-nearest (`+`, `*`, `/`, `Float.sqrt`, `Float.fma`, all with a logical
model in core Lean). Their values are never trusted. Only the *error terms*
are rounded, by directed operations chosen so that each error term is a
one-sided bound of an exact algebraic identity (for any value of the
approximations). Example, `addLo`: with `s := ah + bh`, `bb := s - ah`,
  `ah + bh - s = (ah - (s - bb)) + (bh - bb)`     (an identity in ℝ),
so `e := RD(RD(ah - RU(s - bb)) + RD(bh - bb)) ≤ ah + bh - s`. In the usual
(no-underflow) case every one of these operations is exact (Knuth TwoSum,
Dekker FastTwoSum, FMA TwoProd), so the directed roundings cost no accuracy.

Soundness therefore needs only "directed rounding is one-sided", which
Interval64 already proves; nothing about round-to-nearest is used.

Infinities / NaN / overflow / underflow: a non-finite intermediate makes a
returned word non-finite (all directed operations propagate them), and the
interval operation then falls back to a sound Interval64 computation.
-/
import Interval128.Fma

namespace Interval128

open Interval64.Directed

/-- A double-double `hi + lo` (both words binary64). -/
structure DD where
  hi : Float
  lo : Float
  deriving Repr, Inhabited

namespace DD

def isFin (d : DD) : Bool := d.hi.isFinite && d.lo.isFinite

/-- Exact sign tests on finite words: `hi + lo ≥ 0 ↔ lo ≥ -hi` (negation is exact). -/
def nonneg (h l : Float) : Bool := decide (-h ≤ l)
def nonpos (h l : Float) : Bool := decide (l ≤ -h)
def pos (h l : Float) : Bool := decide (-h < l)
def neg (h l : Float) : Bool := decide (l < -h)

/-- Lower bound of `(ah + al) + (bh + bl)`. -/
def addLo (ah al bh bl : Float) : DD :=
  let s := ah + bh
  let bb := s - ah
  let e := addDown (subDown ah (subUp s bb)) (subDown bh bb)
  let t := al + bl
  let cc := t - al
  let f := addDown (subDown al (subUp t cc)) (subDown bl cc)
  let e2 := addDown e t
  let s2 := s + e2
  let g := addDown (subDown s s2) e2
  let e3 := addDown g f
  let s3 := s2 + e3
  ⟨s3, addDown (subDown s2 s3) e3⟩

/-- Upper bound of `(ah + al) + (bh + bl)`. -/
def addHi (ah al bh bl : Float) : DD :=
  let s := ah + bh
  let bb := s - ah
  let e := addUp (subUp ah (subDown s bb)) (subUp bh bb)
  let t := al + bl
  let cc := t - al
  let f := addUp (subUp al (subDown t cc)) (subUp bl cc)
  let e2 := addUp e t
  let s2 := s + e2
  let g := addUp (subUp s s2) e2
  let e3 := addUp g f
  let s3 := s2 + e3
  ⟨s3, addUp (subUp s2 s3) e3⟩

/-- Lower bound of `(ah + al) * (bh + bl)`. -/
def mulLo (ah al bh bl : Float) : DD :=
  let p := ah * bh
  let e := fmaDown ah bh (-p)
  let c := addDown (addDown (mulDown ah bl) (mulDown al bh)) (mulDown al bl)
  let e2 := addDown e c
  let s := p + e2
  ⟨s, addDown (subDown p s) e2⟩

/-- Upper bound of `(ah + al) * (bh + bl)`. -/
def mulHi (ah al bh bl : Float) : DD :=
  let p := ah * bh
  let e := fmaUp ah bh (-p)
  let c := addUp (addUp (mulUp ah bl) (mulUp al bh)) (mulUp al bl)
  let e2 := addUp e c
  let s := p + e2
  ⟨s, addUp (subUp p s) e2⟩

/-- Lower bound of `R / B` from `r ≤ R` and `dLo ≤ B ≤ dHi`, `B > 0`
    (`-∞` when a denominator bound is unusable). -/
def quotLo (r dLo dHi : Float) : Float :=
  if decide (0 ≤ r) then
    (if decide (0 < dHi) && decide (dHi < Float.inf) then divDown r dHi else -Float.inf)
  else
    (if decide (0 < dLo) && decide (dLo < Float.inf) then divDown r dLo else -Float.inf)

/-- Upper bound of `R / B` from `R ≤ r` and `dLo ≤ B ≤ dHi`, `B > 0`. -/
def quotHi (r dLo dHi : Float) : Float :=
  if decide (0 ≤ r) then
    (if decide (0 < dLo) && decide (dLo < Float.inf) then divUp r dLo else Float.inf)
  else
    (if decide (0 < dHi) && decide (dHi < Float.inf) then divUp r dHi else Float.inf)

/-- Lower bound of `(ah + al) / (bh + bl)`, for `bh + bl > 0`.
    `T = q₁ + q₂ + R/B` with `R = A - (q₁ + q₂) B` (exact identity). -/
def divLo (ah al bh bl : Float) : DD :=
  let q1 := ah / bh
  let r1 := fmaDown (-q1) bh ah
  let q2 := Float.fma (-q1) bl (r1 + al) / bh
  let x := addDown (addDown r1 al) (mulDown (-q1) bl)
  let p2 := q2 * bh
  let e2 := fmaUp q2 bh (-p2)
  let r := addDown (subDown (subDown x p2) e2) (mulDown (-q2) bl)
  let c := quotLo r (addDown bh bl) (addUp bh bl)
  let s := q1 + q2
  let e := addDown (addDown (subDown q1 s) q2) c
  let s2 := s + e
  ⟨s2, addDown (subDown s s2) e⟩

/-- Upper bound of `(ah + al) / (bh + bl)`, for `bh + bl > 0`. -/
def divHi (ah al bh bl : Float) : DD :=
  let q1 := ah / bh
  let r1 := fmaUp (-q1) bh ah
  let q2 := Float.fma (-q1) bl (r1 + al) / bh
  let x := addUp (addUp r1 al) (mulUp (-q1) bl)
  let p2 := q2 * bh
  let e2 := fmaDown q2 bh (-p2)
  let r := addUp (subUp (subUp x p2) e2) (mulUp (-q2) bl)
  let c := quotHi r (addDown bh bl) (addUp bh bl)
  let s := q1 + q2
  let e := addUp (addUp (subUp q1 s) q2) c
  let s2 := s + e
  ⟨s2, addUp (subUp s s2) e⟩

/-- Lower bound of `√(ah + al)`, for `ah + al ≥ 0`.
    `√A = s + (A - s²) / (√A + s)` for `s > 0`. -/
def sqrtLo (ah al : Float) : DD :=
  let s := Float.sqrt ah
  if decide (0 < s) then
    let r := addDown (fmaDown (-s) s ah) al
    let c := quotLo r (addDown (sqrtDown (addDown ah al)) s) (addUp (sqrtUp (addUp ah al)) s)
    let s2 := s + c
    ⟨s2, addDown (subDown s s2) c⟩
  else ⟨-Float.inf, 0⟩

/-- Upper bound of `√(ah + al)`, for `ah + al ≥ 0`. -/
def sqrtHi (ah al : Float) : DD :=
  let s := Float.sqrt ah
  if decide (0 < s) then
    let r := addUp (fmaUp (-s) s ah) al
    let c := quotHi r (addDown (sqrtDown (addDown ah al)) s) (addUp (sqrtUp (addUp ah al)) s)
    let s2 := s + c
    ⟨s2, addUp (subUp s s2) c⟩
  else ⟨Float.inf, 0⟩

/-- Lower bound of `min (a) (b)` (exact values of the pairs). -/
def minLo (a b : DD) : DD :=
  let u := addHi a.hi a.lo (-b.hi) (-b.lo)
  if u.isFin && nonpos u.hi u.lo then a
  else
    let w := addLo a.hi a.lo (-b.hi) (-b.lo)
    if w.isFin && pos w.hi w.lo then b
    else addLo a.hi a.lo (-u.hi) (-u.lo)

/-- Upper bound of `max (a) (b)`. -/
def maxHi (a b : DD) : DD :=
  let w := addLo a.hi a.lo (-b.hi) (-b.lo)
  if w.isFin && nonneg w.hi w.lo then a
  else
    let u := addHi a.hi a.lo (-b.hi) (-b.lo)
    if u.isFin && neg u.hi u.lo then b
    else addHi a.hi a.lo (-w.hi) (-w.lo)

end DD
end Interval128
