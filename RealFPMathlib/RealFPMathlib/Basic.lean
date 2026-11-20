/-
Bridge from the Mathlib-free Interval64 core to Mathlib's real numbers.

* `Float.toReal?` : exact real value of a finite double (`none` for ±∞, NaN).
* `Interval64.toSet` : the set of reals enclosed by an interval. Endpoints
  are read in the extended reals: a `-∞` lower end (or `+∞` upper end) gives
  an unbounded set; a NaN endpoint (or `+∞` lower / `-∞` upper end) gives `∅`.
  For finite endpoints `toSet = Set.Icc lo hi` (`toSet_eq_Icc`).
* `RepresentableR`, `IsRoundDownR`, `IsRoundUpR` : real versions of the core
  `Representable`, `IsRoundDown`, `IsRoundUp`, with transfer lemmas.

Everything here is proved from the core theorems through `Rat.cast` lemmas.
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Interval64
import Interval64Proofs

open Interval64 Interval64.Spec
open Interval64Proofs.Value Interval64Proofs.AddBits Interval64Proofs.FloatBits
open Interval64Proofs.Grid

/-- Exact real value of a finite double; `none` for `±∞` and NaN. -/
def Float.toReal? (f : Float) : Option ℝ := (bitsToRat? f.toBits).map (fun q => (q : ℝ))

/-- Exact real value of a double, with the junk value `0` for `±∞` and NaN. -/
def Float.toReal (f : Float) : ℝ := ((bitsToRat? f.toBits).getD 0 : ℚ)

namespace RealFP

/-- Real lower-endpoint enclosure: `v ≤ x` in the extended reals
    (`-∞` encloses every real; `+∞` and NaN enclose none). -/
def loR : Option EVal → ℝ → Prop
  | some .negInf, _ => True
  | some (.rat q), x => (q : ℝ) ≤ x
  | some .posInf, _ => False
  | none, _ => False

/-- Real upper-endpoint enclosure: `x ≤ v` in the extended reals. -/
def hiR : Option EVal → ℝ → Prop
  | some .posInf, _ => True
  | some (.rat q), x => x ≤ (q : ℝ)
  | some .negInf, _ => False
  | none, _ => False

@[simp] theorem loR_rat (q : ℚ) (x : ℝ) : loR (some (.rat q)) x ↔ (q : ℝ) ≤ x := Iff.rfl
@[simp] theorem hiR_rat (q : ℚ) (x : ℝ) : hiR (some (.rat q)) x ↔ x ≤ (q : ℝ) := Iff.rfl

theorem loR_cast (v : Option EVal) (q : ℚ) : loR v (q : ℝ) ↔ loEncloses? v q := by
  rcases v with _ | (_ | r | _) <;> simp [loR, loEncloses?, loEncloses]

theorem hiR_cast (v : Option EVal) (q : ℚ) : hiR v (q : ℝ) ↔ hiEncloses? v q := by
  rcases v with _ | (_ | r | _) <;> simp [hiR, hiEncloses?, hiEncloses]

theorem loR_mono {v : Option EVal} {a b : ℝ} (h : loR v a) (hab : a ≤ b) : loR v b := by
  rcases v with _ | (_ | r | _) <;> simp_all [loR]
  exact le_trans h hab

theorem hiR_mono {v : Option EVal} {a b : ℝ} (h : hiR v b) (hab : a ≤ b) : hiR v a := by
  rcases v with _ | (_ | r | _) <;> simp_all [hiR]
  exact le_trans hab h

end RealFP

open RealFP

set_option linter.dupNamespace false in
/-- The set of reals enclosed by an interval (extended-real reading of the
    endpoints; empty when an endpoint is NaN). -/
def Interval64.Interval64.toSet (I : Interval64) : Set ℝ :=
  {x | loR (bitsToEVal I.lo.toBits) x ∧ hiR (bitsToEVal I.hi.toBits) x}

namespace RealFP

theorem mem_toSet {I : Interval64} {x : ℝ} :
    x ∈ I.toSet ↔ loR (bitsToEVal I.lo.toBits) x ∧ hiR (bitsToEVal I.hi.toBits) x := Iff.rfl

/-- On rationals, `toSet` membership is the core `MemIv`. -/
theorem cast_mem_toSet_iff {I : Interval64} {q : ℚ} : (q : ℝ) ∈ I.toSet ↔ MemIv q I := by
  rw [mem_toSet, loR_cast, hiR_cast]; rfl

theorem toReal?_eq_some {f : Float} {x : ℝ} :
    f.toReal? = some x ↔ ∃ q : ℚ, bitsToRat? f.toBits = some q ∧ (q : ℝ) = x := by
  unfold Float.toReal?
  cases bitsToRat? f.toBits <;> simp

theorem toReal?_of_bitsToRat? {f : Float} {q : ℚ} (h : bitsToRat? f.toBits = some q) :
    f.toReal? = some (q : ℝ) := by
  simp [Float.toReal?, h]

theorem toReal_of_bitsToRat? {f : Float} {q : ℚ} (h : bitsToRat? f.toBits = some q) :
    f.toReal = (q : ℝ) := by
  simp [Float.toReal, h]

/-- For finite endpoints, `toSet` is a closed real interval. -/
theorem toSet_eq_Icc {I : Interval64} {l h : ℚ}
    (hl : bitsToRat? I.lo.toBits = some l) (hh : bitsToRat? I.hi.toBits = some h) :
    I.toSet = Set.Icc (l : ℝ) (h : ℝ) := by
  ext x
  rw [mem_toSet, bitsToEVal_rat_of_bitsToRat? hl, bitsToEVal_rat_of_bitsToRat? hh]
  simp

/-- `toSet` is convex. -/
theorem mem_toSet_of_between {I : Interval64} {a b z : ℝ} (ha : a ∈ I.toSet)
    (hb : b ∈ I.toSet) (haz : a ≤ z) (hzb : z ≤ b) : z ∈ I.toSet :=
  ⟨loR_mono ha.1 haz, hiR_mono hb.2 hzb⟩

/-- Every real in `I.toSet` has a rational point of `I` at or below it. -/
theorem exists_rat_le_of_mem {I : Interval64} {x : ℝ} (hx : x ∈ I.toSet) :
    ∃ q : ℚ, MemIv q I ∧ (q : ℝ) ≤ x := by
  rcases hlo : bitsToEVal I.lo.toBits with _ | (_ | l | _)
  · have := hx.1; rw [hlo] at this; exact this.elim
  · refine ⟨(⌊x⌋ : ℚ), ?_, ?_⟩
    · rw [← cast_mem_toSet_iff]
      refine ⟨?_, hiR_mono hx.2 ?_⟩
      · rw [hlo]; trivial
      · push_cast; exact Int.floor_le x
    · push_cast; exact Int.floor_le x
  · have hl : (l : ℝ) ≤ x := by have := hx.1; rw [hlo] at this; exact this
    refine ⟨l, ?_, hl⟩
    rw [← cast_mem_toSet_iff]
    exact ⟨by rw [hlo]; exact le_refl _, hiR_mono hx.2 hl⟩
  · have := hx.1; rw [hlo] at this; exact this.elim

/-- Every real in `I.toSet` has a rational point of `I` at or above it. -/
theorem exists_rat_ge_of_mem {I : Interval64} {x : ℝ} (hx : x ∈ I.toSet) :
    ∃ q : ℚ, MemIv q I ∧ x ≤ (q : ℝ) := by
  rcases hhi : bitsToEVal I.hi.toBits with _ | (_ | h | _)
  · have := hx.2; rw [hhi] at this; exact this.elim
  · have := hx.2; rw [hhi] at this; exact this.elim
  · have hh : x ≤ (h : ℝ) := by have := hx.2; rw [hhi] at this; exact this
    refine ⟨h, ?_, hh⟩
    rw [← cast_mem_toSet_iff]
    exact ⟨loR_mono hx.1 hh, by rw [hhi]; exact le_refl _⟩
  · refine ⟨(⌈x⌉ : ℚ), ?_, ?_⟩
    · rw [← cast_mem_toSet_iff]
      refine ⟨loR_mono hx.1 ?_, ?_⟩
      · push_cast; exact Int.le_ceil x
      · rw [hhi]; trivial
    · push_cast; exact Int.le_ceil x

/-- A real lies in `Z.toSet` once it is squeezed between two rational points of `Z`. -/
theorem mem_toSet_of_rat_bounds {Z : Interval64} {x : ℝ} {p q : ℚ}
    (hp : MemIv p Z) (hq : MemIv q Z) (hpx : (p : ℝ) ≤ x) (hxq : x ≤ (q : ℝ)) :
    x ∈ Z.toSet :=
  mem_toSet_of_between (cast_mem_toSet_iff.2 hp) (cast_mem_toSet_iff.2 hq) hpx hxq

/-- Upper bound from a compiled comparison (`native_decide`) on the upper endpoint. -/
theorem le_of_mem_toSet_of_hi_le {I : Interval64} {x : ℝ} {c : Float} {q : ℚ}
    (hx : x ∈ I.toSet) (hle : I.hi ≤ c) (hc : bitsToRat? c.toBits = some q) : x ≤ (q : ℝ) := by
  obtain ⟨p, hp, hxp⟩ := exists_rat_ge_of_mem hx
  exact le_trans hxp (by exact_mod_cast hi_le_of_native hp hle hc)

/-! ### Representability and directed rounding over `ℝ` -/

/-- A real is representable when it is the exact value of some finite binary64. -/
def RepresentableR (x : ℝ) : Prop := ∃ q : ℚ, Representable q ∧ (q : ℝ) = x

theorem representableR_iff_exists_float (x : ℝ) :
    RepresentableR x ↔ ∃ f : Float, f.toReal? = some x := by
  constructor
  · rintro ⟨q, ⟨b, hb⟩, rfl⟩
    exact ⟨Float.ofRatDown q, toReal?_of_bitsToRat? (Interval64Proofs.OfRat.ofRat_exact_iv ⟨b, hb⟩).1⟩
  · rintro ⟨f, hf⟩
    obtain ⟨q, hq, rfl⟩ := toReal?_eq_some.1 hf
    exact ⟨q, ⟨_, hq⟩, rfl⟩

@[simp] theorem representableR_cast (q : ℚ) : RepresentableR (q : ℝ) ↔ Representable q := by
  constructor
  · rintro ⟨r, hr, he⟩
    rw [Rat.cast_inj.1 he] at hr; exact hr
  · intro h; exact ⟨q, h, rfl⟩

/-- `r` is the greatest representable real `≤ x` (`-∞` if none). -/
def IsRoundDownR (x : ℝ) (r : Option EVal) : Prop :=
  loR r x ∧ ∀ v, RepresentableR v → v ≤ x → hiR r v

/-- `r` is the least representable real `≥ x` (`+∞` if none). -/
def IsRoundUpR (x : ℝ) (r : Option EVal) : Prop :=
  hiR r x ∧ ∀ v, RepresentableR v → x ≤ v → loR r v

theorem isRoundDownR_cast_iff (q : ℚ) (r : Option EVal) :
    IsRoundDownR (q : ℝ) r ↔ IsRoundDown q r := by
  unfold IsRoundDownR IsRoundDown
  rw [loR_cast]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun v hv hle => (hiR_cast r v).1
      (h2 v ((representableR_cast v).2 hv) (by exact_mod_cast hle))⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro v ⟨w, hw, rfl⟩ hle
    exact (hiR_cast r w).2 (h2 w hw (by exact_mod_cast hle))

theorem isRoundUpR_cast_iff (q : ℚ) (r : Option EVal) :
    IsRoundUpR (q : ℝ) r ↔ IsRoundUp q r := by
  unfold IsRoundUpR IsRoundUp
  rw [hiR_cast]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun v hv hle => (loR_cast r v).1
      (h2 v ((representableR_cast v).2 hv) (by exact_mod_cast hle))⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro v ⟨w, hw, rfl⟩ hle
    exact (loR_cast r w).2 (h2 w hw (by exact_mod_cast hle))

/-- No representable real lies strictly between a round-down result and the exact value. -/
theorem IsRoundDownR.no_between {x : ℝ} {d : ℚ} {v : ℝ} (h : IsRoundDownR x (some (.rat d)))
    (hv : RepresentableR v) (hdv : (d : ℝ) < v) : x < v :=
  lt_of_not_ge fun hle => absurd (h.2 v hv hle) (by simpa using hdv)

/-- No representable real lies strictly between the exact value and a round-up result. -/
theorem IsRoundUpR.no_between {x : ℝ} {u : ℚ} {v : ℝ} (h : IsRoundUpR x (some (.rat u)))
    (hv : RepresentableR v) (hvu : v < (u : ℝ)) : v < x :=
  lt_of_not_ge fun hle => absurd (h.2 v hv hle) (by simpa using hvu)

/-- A round-down result with a finite value is `≤` the exact real. -/
theorem IsRoundDownR.le {x : ℝ} {f : Float} {d : ℝ} (h : IsRoundDownR x (bitsToEVal f.toBits))
    (hf : f.toReal? = some d) : d ≤ x := by
  obtain ⟨q, hq, rfl⟩ := toReal?_eq_some.1 hf
  have := h.1; rwa [bitsToEVal_rat_of_bitsToRat? hq] at this

/-- A round-up result with a finite value is `≥` the exact real. -/
theorem IsRoundUpR.ge {x : ℝ} {f : Float} {u : ℝ} (h : IsRoundUpR x (bitsToEVal f.toBits))
    (hf : f.toReal? = some u) : x ≤ u := by
  obtain ⟨q, hq, rfl⟩ := toReal?_eq_some.1 hf
  have := h.1; rwa [bitsToEVal_rat_of_bitsToRat? hq] at this

end RealFP
