/-
Correctness of the kernel interval fast path: `toI (KI.op X ...) = Interval64.op (toI X) ...`
for well-formed (`< 2^64`) bit patterns.
-/
import Interval64Proofs.KernelFloat
import Interval64.Kernel.Interval
import Interval64.Ops

set_option linter.unusedSimpArgs false

namespace Interval64.KF

open Interval64.Spec
open Float.Model Float.Model.UnpackedFloat

/-! ### Constants -/

theorem toF_zero : toF 0 = (0 : Float) := by decide +kernel
theorem toF_zero' : toF 0 = (0.0 : Float) := by decide +kernel
theorem toF_one : toF KI.oneBits = (1 : Float) := by decide +kernel
theorem toF_qNaN : toF qNaN = Float.nan := by decide +kernel
theorem toF_inf : toF infBits = Float.inf := by decide +kernel
theorem toF_negInf : toF KI.negInfBits = -Float.inf := by decide +kernel

theorem isNaN_false_of_isInf {x : Nat} (h : isInf x = true) : isNaN x = false := by
  rw [isInf_iff] at h
  cases hn : isNaN x
  · rfl
  · rw [isNaN_iff] at hn; omega

theorem isInf_toF' {x : Nat} (hx : x < 2 ^ 64) : (toF x).isInf = isInf x := by
  rw [isInf_toF hx]
  cases hi : isInf x
  · simp
  · simp [isNaN_false_of_isInf hi]

theorem toBits_toF_of_not_nan {x : Nat} (hx : x < 2 ^ 64) (hn : isNaN x = false) :
    (toF x).toBits = UInt64.ofNat x := by
  apply UInt64.toNat_inj.mp
  rw [toNat_toBits_toF hx, UInt64.toNat_ofNat_of_lt' hx]
  unfold canon; simp [hn]

theorem toF_ofBits (u : UInt64) : Float.ofBits u = toF u.toNat := (toF_toNat u).symm

/-! ### Intervals -/

/-- The `Interval64` denoted by a pair of bit patterns. -/
def toI (a : KI) : Interval64 := ⟨toF a.lo, toF a.hi⟩

/-- Both bit patterns fit in 64 bits. -/
def WF (a : KI) : Prop := a.lo < 2 ^ 64 ∧ a.hi < 2 ^ 64

theorem toI_invalid : toI KI.invalid = invalid := by
  show (⟨toF qNaN, toF qNaN⟩ : Interval64) = ⟨Float.nan, Float.nan⟩; rw [toF_qNaN]
theorem toI_whole : toI KI.whole = whole := by
  show (⟨toF KI.negInfBits, toF infBits⟩ : Interval64) = ⟨-Float.inf, Float.inf⟩
  rw [toF_negInf, toF_inf]
theorem toI_one : toI KI.one = ⟨1, 1⟩ := by
  show (⟨toF KI.oneBits, toF KI.oneBits⟩ : Interval64) = _; rw [toF_one]

theorem wf_invalid : WF KI.invalid := ⟨by decide, by decide⟩
theorem wf_whole : WF KI.whole := ⟨by decide, by decide⟩
theorem wf_one : WF KI.one := ⟨by decide, by decide⟩
theorem zero_lt : (0 : Nat) < 2 ^ 64 := by decide
theorem oneBits_lt : KI.oneBits < 2 ^ 64 := by decide
theorem negBits_lt {x : Nat} (h : x < 2 ^ 64) : negBits x < 2 ^ 64 := (negBits_fields h).1

theorem fmin_toF {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    fmin (toF x) (toF y) = toF (KI.fmin x y) := by
  unfold fmin KI.fmin; rw [lt_toF hx hy]; cases lt x y <;> rfl
theorem fmax_toF {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    fmax (toF x) (toF y) = toF (KI.fmax x y) := by
  unfold fmax KI.fmax
  show (if decide (toF y < toF x) = true then _ else _) = _
  rw [lt_toF hy hx]; cases lt y x <;> rfl
theorem fmin_lt {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) : KI.fmin x y < 2 ^ 64 := by
  unfold KI.fmin; cases lt x y <;> assumption
theorem fmax_lt {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) : KI.fmax x y < 2 ^ 64 := by
  unfold KI.fmax; cases lt y x <;> assumption

theorem anyNan_toI {a b : KI} (ha : WF a) (hb : WF b) :
    anyNan (toI a) (toI b) = KI.anyNan a b := by
  unfold anyNan KI.anyNan toI
  simp only [isNaN_toF ha.1, isNaN_toF ha.2, isNaN_toF hb.1, isNaN_toF hb.2]

theorem add_toI {a b : KI} (ha : WF a) (hb : WF b) : toI (KI.add a b) = toI a + toI b := by
  show _ = Interval64.add _ _
  unfold Interval64.add KI.add
  rw [anyNan_toI ha hb]
  cases KI.anyNan a b
  · show toI ⟨_, _⟩ = _
    simp only [toI, addDown_toF ha.1 hb.1, addUp_toF ha.2 hb.2]; rfl
  · exact toI_invalid

theorem add_wf {a b : KI} (ha : WF a) (hb : WF b) : WF (KI.add a b) := by
  unfold KI.add; cases KI.anyNan a b
  · exact ⟨add_lt ha.1 hb.1 _, add_lt ha.2 hb.2 _⟩
  · exact wf_invalid

theorem sub_toI {a b : KI} (ha : WF a) (hb : WF b) : toI (KI.sub a b) = toI a - toI b := by
  show _ = Interval64.sub _ _
  unfold Interval64.sub KI.sub
  rw [anyNan_toI ha hb]
  cases KI.anyNan a b
  · show toI ⟨_, _⟩ = _
    simp only [toI, subDown_toF ha.1 hb.2, subUp_toF ha.2 hb.1]; rfl
  · exact toI_invalid

theorem sub_wf {a b : KI} (ha : WF a) (hb : WF b) : WF (KI.sub a b) := by
  unfold KI.sub; cases KI.anyNan a b
  · exact ⟨sub_lt ha.1 hb.2 _, sub_lt ha.2 hb.1 _⟩
  · exact wf_invalid

theorem neg_toI {a : KI} (ha : WF a) : toI (KI.neg a) = -toI a := by
  show _ = Interval64.neg _
  unfold Interval64.neg KI.neg toI
  simp only [neg_toF ha.1, neg_toF ha.2]

theorem neg_wf {a : KI} (ha : WF a) : WF (KI.neg a) := ⟨negBits_lt ha.2, negBits_lt ha.1⟩

theorem hull_toI {a b : KI} (ha : WF a) (hb : WF b) : toI (KI.hull a b) = hull (toI a) (toI b) := by
  unfold hull KI.hull
  simp only [toI, isNaN_toF ha.1, isNaN_toF ha.2, isNaN_toF hb.1, isNaN_toF hb.2]
  cases isNaN a.lo || isNaN a.hi
  · cases isNaN b.lo || isNaN b.hi
    · simp [cond, fmin_toF ha.1 hb.1, fmax_toF ha.2 hb.2]
    · simp [cond]
  · simp [cond]

theorem hull_wf {a b : KI} (ha : WF a) (hb : WF b) : WF (KI.hull a b) := by
  unfold KI.hull
  cases isNaN a.lo || isNaN a.hi
  · cases isNaN b.lo || isNaN b.hi
    · exact ⟨fmin_lt ha.1 hb.1, fmax_lt ha.2 hb.2⟩
    · exact ha
  · exact hb

theorem sqrt_toI {a : KI} (ha : WF a) : toI (KI.sqrt a) = Interval64.sqrt (toI a) := by
  unfold Interval64.sqrt KI.sqrt
  simp only [toI, isNaN_toF ha.1, isNaN_toF ha.2, ← toF_zero, ← toF_zero', lt_toF ha.2 zero_lt,
    lt_toF ha.1 zero_lt]
  cases isNaN a.lo || isNaN a.hi
  · cases lt a.hi 0
    · cases lt a.lo 0
      · simp [cond, sqrtDown_toF ha.1, sqrtUp_toF ha.2]
      · simp [cond, sqrtDown_toF zero_lt, sqrtUp_toF ha.2]
    · simp [cond, toF_qNaN, invalid, KI.invalid]
  · simp [cond, toF_qNaN, invalid, KI.invalid]

theorem sqrt_wf {a : KI} (ha : WF a) : WF (KI.sqrt a) := by
  unfold KI.sqrt
  cases isNaN a.lo || isNaN a.hi
  · cases lt a.hi 0
    · exact ⟨sqrt_lt (by cases lt a.lo 0 <;> simp [cond, ha.1, zero_lt]) _, sqrt_lt ha.2 _⟩
    · exact wf_invalid
  · exact wf_invalid

theorem toI_cond (c : Bool) (X Y : KI) : toI (bif c then X else Y) = if c = true then toI X else toI Y := by
  cases c <;> rfl

theorem toF_cond (c : Bool) (x y : Nat) : toF (bif c then x else y) = if c = true then toF x else toF y := by
  cases c <;> rfl

theorem toI_mk (x y : Nat) : toI ⟨x, y⟩ = ⟨toF x, toF y⟩ := rfl

theorem containsZero_toI {a : KI} (ha : WF a) : containsZero (toI a) = KI.containsZero a := by
  unfold containsZero KI.containsZero isInvalid KI.isInvalid
  simp only [toI, isNaN_toF ha.1, isNaN_toF ha.2, ← toF_zero, le_toF ha.1 zero_lt, le_toF zero_lt ha.2]

theorem inv_toI {a : KI} (ha : WF a) : toI (KI.inv a) = inv (toI a) := by
  unfold inv KI.inv
  rw [containsZero_toI ha]
  simp only [toI_cond, toI_mk, toI_invalid, toI_whole]
  simp only [toI, isNaN_toF ha.1, isNaN_toF ha.2, ← toF_one, divDown_toF oneBits_lt ha.2,
    divUp_toF oneBits_lt ha.1]

theorem inv_wf {a : KI} (ha : WF a) : WF (KI.inv a) := by
  unfold KI.inv
  cases isNaN a.lo || isNaN a.hi
  · cases KI.containsZero a
    · exact ⟨div_lt oneBits_lt ha.2 _, div_lt oneBits_lt ha.1 _⟩
    · exact wf_whole
  · exact wf_invalid

theorem abs_toI {a : KI} (ha : WF a) : toI (KI.abs a) = Interval64.abs (toI a) := by
  unfold Interval64.abs KI.abs
  simp only [toI_cond, toI_mk, toI_invalid]
  simp only [toI, isNaN_toF ha.1, isNaN_toF ha.2, ← toF_zero, le_toF zero_lt ha.1, le_toF ha.2 zero_lt,
    neg_toF ha.1, neg_toF ha.2, fmax_toF (negBits_lt ha.1) ha.2]

theorem abs_wf {a : KI} (ha : WF a) : WF (KI.abs a) := by
  unfold KI.abs
  cases isNaN a.lo || isNaN a.hi
  · cases le 0 a.lo
    · cases le a.hi 0
      · exact ⟨zero_lt, fmax_lt (negBits_lt ha.1) ha.2⟩
      · exact ⟨negBits_lt ha.2, negBits_lt ha.1⟩
    · exact ha
  · exact wf_invalid

theorem square_toI {a : KI} (ha : WF a) : toI (KI.square a) = square (toI a) := by
  unfold square KI.square
  simp only [toI_cond, toI_mk, toI_invalid]
  simp only [toI, isNaN_toF ha.1, isNaN_toF ha.2, ← toF_zero, le_toF zero_lt ha.1, le_toF ha.2 zero_lt,
    mulDown_toF ha.1 ha.1, mulUp_toF ha.2 ha.2, mulDown_toF ha.2 ha.2, mulUp_toF ha.1 ha.1,
    fmax_toF (mul_lt ha.1 ha.1 true) (mul_lt ha.2 ha.2 true)]

theorem square_wf {a : KI} (ha : WF a) : WF (KI.square a) := by
  unfold KI.square
  cases isNaN a.lo || isNaN a.hi
  · cases le 0 a.lo
    · cases le a.hi 0
      · exact ⟨zero_lt, fmax_lt (mul_lt ha.1 ha.1 _) (mul_lt ha.2 ha.2 _)⟩
      · exact ⟨mul_lt ha.2 ha.2 _, mul_lt ha.1 ha.1 _⟩
    · exact ⟨mul_lt ha.1 ha.1 _, mul_lt ha.2 ha.2 _⟩
  · exact wf_invalid

theorem accCorner_toF {x y lo hi : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (hl : lo < 2 ^ 64)
    (hh : hi < 2 ^ 64) (got : Bool) :
    accCorner (toF x) (toF y) (toF lo) (toF hi) got =
      ((toF (KI.accCorner x y lo hi got).1, toF (KI.accCorner x y lo hi got).2.1,
        (KI.accCorner x y lo hi got).2.2)) := by
  unfold accCorner KI.accCorner
  simp only [← toF_zero, beq_toF hx zero_lt, beq_toF hy zero_lt, isInf_toF' hx, isInf_toF' hy,
    mulDown_toF hx hy, mulUp_toF hx hy, isNaN_toF (mul_lt hx hy false), isNaN_toF (mul_lt hx hy true),
    lt_toF (mul_lt hx hy false) hl, GT.gt, lt_toF hh (mul_lt hx hy true)]
  cases (beq x 0 && isInf y || beq y 0 && isInf x)
  · cases (isNaN (mul x y false) || isNaN (mul x y true))
    · cases got
      · simp [cond]
      · cases lt (mul x y false) lo <;> cases lt hi (mul x y true) <;> simp [cond]
    · simp [cond]
  · simp [cond]

theorem accCorner_lt {x y lo hi : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (hl : lo < 2 ^ 64)
    (hh : hi < 2 ^ 64) (got : Bool) :
    (KI.accCorner x y lo hi got).1 < 2 ^ 64 ∧ (KI.accCorner x y lo hi got).2.1 < 2 ^ 64 := by
  unfold KI.accCorner; dsimp only
  have hd := mul_lt hx hy false
  have hu := mul_lt hx hy true
  generalize mul x y false = d at *
  generalize mul x y true = u at *
  cases (beq x 0 && isInf y || beq y 0 && isInf x) <;> cases (isNaN d || isNaN u) <;> cases got <;>
    cases lt d lo <;> cases lt hi u <;> simp [cond, *]

theorem accStep_toF {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (r : Nat × Nat × Bool)
    (hr : r.1 < 2 ^ 64 ∧ r.2.1 < 2 ^ 64) :
    accCorner (toF x) (toF y) (toF r.1) (toF r.2.1) r.2.2 =
      ((toF (KI.accStep x y r).1, toF (KI.accStep x y r).2.1, (KI.accStep x y r).2.2)) :=
  accCorner_toF hx hy hr.1 hr.2 r.2.2

theorem accStep_lt {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (r : Nat × Nat × Bool)
    (hr : r.1 < 2 ^ 64 ∧ r.2.1 < 2 ^ 64) :
    (KI.accStep x y r).1 < 2 ^ 64 ∧ (KI.accStep x y r).2.1 < 2 ^ 64 :=
  accCorner_lt hx hy hr.1 hr.2 r.2.2

theorem mul_toI {a b : KI} (ha : WF a) (hb : WF b) : toI (KI.mul a b) = toI a * toI b := by
  show _ = Interval64.mul _ _
  unfold Interval64.mul KI.mul
  rw [anyNan_toI ha hb]
  cases KI.anyNan a b
  · simp only [Bool.cond_false, Bool.false_eq_true, ite_false]
    have h1 := accCorner_lt ha.1 hb.1 zero_lt zero_lt false
    have h2 := accStep_lt ha.1 hb.2 _ h1
    have h3 := accStep_lt ha.2 hb.1 _ h2
    simp only [toI, ← toF_zero, accCorner_toF ha.1 hb.1 zero_lt zero_lt false,
      accStep_toF ha.1 hb.2 _ h1, accStep_toF ha.2 hb.1 _ h2, accStep_toF ha.2 hb.2 _ h3]
    generalize KI.accStep a.hi b.hi _ = r4
    unfold KI.mulEnd
    cases r4.2.2
    · exact toI_whole
    · rfl
  · exact toI_invalid

theorem mul_wf {a b : KI} (ha : WF a) (hb : WF b) : WF (KI.mul a b) := by
  unfold KI.mul
  cases KI.anyNan a b
  · simp only [Bool.cond_false]
    have h1 := accCorner_lt ha.1 hb.1 zero_lt zero_lt false
    generalize KI.accCorner a.lo b.lo 0 0 false = r1 at *
    have h2 := accStep_lt ha.1 hb.2 r1 h1
    generalize KI.accStep a.lo b.hi r1 = r2 at *
    have h3 := accStep_lt ha.2 hb.1 r2 h2
    generalize KI.accStep a.hi b.lo r2 = r3 at *
    have h4 := accStep_lt ha.2 hb.2 r3 h3
    generalize KI.accStep a.hi b.hi r3 = r4 at *
    unfold KI.mulEnd
    cases r4.2.2
    · exact wf_whole
    · exact h4
  · exact wf_invalid

theorem beq_nat_eq (a b : Nat) : (a == b) = Nat.beq a b := rfl

theorem ipowAux_toI (fuel : Nat) : ∀ (b : KI) (e : Nat) (acc : KI), WF b → WF acc →
    toI (KI.ipowAux fuel b e acc) = ipowAux fuel (toI b) e (toI acc) ∧
      WF (KI.ipowAux fuel b e acc) := by
  induction fuel with
  | zero =>
    intro b e acc hb hacc
    unfold KI.ipowAux ipowAux
    simp only [beq_nat_eq]
    by_cases h : Nat.beq e 0 = true
    · simp only [h, ite_true, Bool.cond_true]; exact ⟨trivial, hacc⟩
    · simp only [h, ite_false, Bool.false_eq_true, Bool.cond_false]; exact ⟨toI_whole, wf_whole⟩
  | succ fuel ih =>
    intro b e acc hb hacc
    unfold KI.ipowAux ipowAux
    simp only [beq_nat_eq]
    by_cases h : Nat.beq e 0 = true
    · simp only [h, ite_true, Bool.cond_true]; exact ⟨trivial, hacc⟩
    · simp only [h, ite_false, Bool.false_eq_true, Bool.cond_false]
      have hsq := square_wf hb
      by_cases h2 : Nat.beq (e % 2) 1 = true
      · have h2' : Nat.beq (Nat.mod e 2) 1 = true := h2
        simp only [h2, h2', ite_true, Bool.cond_true]
        have := ih (KI.square b) (Nat.div e 2) (KI.mul acc b) hsq (mul_wf hacc hb)
        rw [this.1, square_toI hb, mul_toI hacc hb]
        exact ⟨rfl, this.2⟩
      · have h2' : ¬ Nat.beq (Nat.mod e 2) 1 = true := h2
        simp only [h2, h2', ite_false, Bool.false_eq_true, Bool.cond_false]
        have := ih (KI.square b) (Nat.div e 2) acc hsq hacc
        rw [this.1, square_toI hb]
        exact ⟨rfl, this.2⟩

theorem ipow_toI {b : KI} (hb : WF b) (e : Nat) :
    toI (KI.ipow b e) = ipow (toI b) e ∧ WF (KI.ipow b e) := by
  unfold KI.ipow ipow
  have := ipowAux_toI 64 b e KI.one hb wf_one
  rw [this.1, toI_one]; exact ⟨rfl, this.2⟩

theorem powLo_toF {f : Nat} (hf : f < 2 ^ 64) (n : Nat) :
    powLo (toF f) n = toF (KI.powLo f n) ∧ KI.powLo f n < 2 ^ 64 := by
  unfold powLo KI.powLo
  rw [isInf_toF' hf]
  cases isInf f
  · have := ipow_toI (b := ⟨f, f⟩) ⟨hf, hf⟩ n
    simp only [Bool.false_eq_true, ite_false, Bool.cond_false]
    exact ⟨by rw [show (⟨toF f, toF f⟩ : Interval64) = toI ⟨f, f⟩ from rfl, ← this.1]; rfl, this.2.1⟩
  · simp only [ite_true, Bool.cond_true]; exact ⟨trivial, hf⟩

theorem powHi_toF {f : Nat} (hf : f < 2 ^ 64) (n : Nat) :
    powHi (toF f) n = toF (KI.powHi f n) ∧ KI.powHi f n < 2 ^ 64 := by
  unfold powHi KI.powHi
  rw [isInf_toF' hf]
  cases isInf f
  · have := ipow_toI (b := ⟨f, f⟩) ⟨hf, hf⟩ n
    simp only [Bool.false_eq_true, ite_false, Bool.cond_false]
    exact ⟨by rw [show (⟨toF f, toF f⟩ : Interval64) = toI ⟨f, f⟩ from rfl, ← this.1]; rfl, this.2.2⟩
  · simp only [ite_true, Bool.cond_true]; exact ⟨trivial, hf⟩

theorem pown_toI {a : KI} (ha : WF a) (n : Nat) :
    toI (KI.pown a n) = pown (toI a) n ∧ WF (KI.pown a n) := by
  unfold pown KI.pown
  have habs := abs_toI ha
  have hw := abs_wf ha
  simp only [toI, isNaN_toF ha.1, isNaN_toF ha.2]
  cases isNaN a.lo || isNaN a.hi
  · simp only [Bool.cond_false, Bool.false_eq_true, ite_false]
    by_cases h0 : (n == 0) = true
    · simp only [h0, ite_true]; exact ⟨toI_one, wf_one⟩
    · simp only [h0, ite_false, Bool.false_eq_true]
      by_cases h1 : (n % 2 == 1) = true
      · simp only [h1, ite_true]
        exact ⟨by rw [(powLo_toF ha.1 n).1, (powHi_toF ha.2 n).1],
          (powLo_toF ha.1 n).2, (powHi_toF ha.2 n).2⟩
      · simp only [h1, ite_false, Bool.false_eq_true]
        have e : Interval64.abs ⟨toF a.lo, toF a.hi⟩ = ⟨toF (KI.abs a).lo, toF (KI.abs a).hi⟩ :=
          habs.symm
        rw [e]
        exact ⟨by rw [(powLo_toF hw.1 n).1, (powHi_toF hw.2 n).1],
          (powLo_toF hw.1 n).2, (powHi_toF hw.2 n).2⟩
  · simp only [Bool.cond_true, ite_true]; exact ⟨toI_invalid, wf_invalid⟩

theorem posInf_toNat : Spec.posInf.toNat = infBits := by decide
theorem negInf_toNat : Spec.negInf.toNat = KI.negInfBits := by decide
theorem qNaN_toNat : Spec.qNaN.toNat = qNaN := by decide

theorem exp_toI {a : KI} (ha : WF a) : toI (KI.exp a) = Interval64.exp (toI a) ∧ WF (KI.exp a) := by
  unfold Interval64.exp KI.exp
  simp only [toI, isNaN_toF ha.1, isNaN_toF ha.2]
  cases h : (isNaN a.lo || isNaN a.hi)
  · simp only [Bool.cond_false, Bool.false_eq_true, ite_false]
    simp only [Bool.or_eq_false_iff] at h
    refine ⟨?_, UInt64.toNat_lt _, UInt64.toNat_lt _⟩
    simp only [Directed.expDown, Directed.expUp, Directed.expDownSpec, Directed.expUpSpec,
      toBits_toF_of_not_nan ha.1 h.1, toBits_toF_of_not_nan ha.2 h.2, toF_ofBits]
  · simp only [Bool.cond_true, ite_true]; exact ⟨toI_invalid, wf_invalid⟩

theorem logLo_toF {x : Nat} (hx : x < 2 ^ 64) (hn : isNaN x = false) :
    logLo (toF x) = toF (KI.logLo x) ∧ KI.logLo x < 2 ^ 64 := by
  unfold logLo KI.logLo
  rw [toBits_toF_of_not_nan hx hn]
  have hb : (Transc.logDownBits (UInt64.ofNat x)).toNat < 2 ^ 64 := UInt64.toNat_lt _
  generalize Spec.unpackBits (UInt64.ofNat x) = u
  cases u
  all_goals first | (rename_i s m e h; cases s) | (rename_i s; cases s) | skip
  all_goals simp [Directed.logDown, Directed.logDownSpec, toF_ofBits, toBits_toF_of_not_nan hx hn,
      posInf_toNat, negInf_toNat, qNaN_toNat, hb]
  all_goals decide

theorem log_toI {a : KI} (ha : WF a) : toI (KI.log a) = Interval64.log (toI a) ∧ WF (KI.log a) := by
  unfold Interval64.log KI.log
  simp only [toI, isNaN_toF ha.1, isNaN_toF ha.2]
  cases h : (isNaN a.lo || isNaN a.hi)
  · simp only [Bool.cond_false, Bool.false_eq_true, ite_false]
    simp only [Bool.or_eq_false_iff] at h
    rw [toBits_toF_of_not_nan ha.2 h.2]
    have hl := logLo_toF ha.1 h.1
    have hb : (Transc.logUpBits (UInt64.ofNat a.hi)).toNat < 2 ^ 64 := UInt64.toNat_lt _
    generalize Spec.unpackBits (UInt64.ofNat a.hi) = u
    cases u
    all_goals first | (rename_i s m e h'; cases s) | (rename_i s; cases s) | skip
    all_goals simp [Directed.logUp, Directed.logUpSpec, toF_ofBits, toBits_toF_of_not_nan ha.2 h.2,
        posInf_toNat, negInf_toNat, qNaN_toNat, hb, hl.1, hl.2, toI_invalid, toI, KI.invalid,
        toF_qNaN, invalid, WF]
    all_goals decide
  · simp only [Bool.cond_true, ite_true]; exact ⟨toI_invalid, wf_invalid⟩

theorem minusOne_toF : minusOne = toF KI.minusOne := (toF_toNat _).symm
theorem plusOne_toF : plusOne = toF KI.plusOne := (toF_toNat _).symm

theorem sin_toI {a : KI} (ha : WF a) : toI (KI.sin a) = Interval64.sin (toI a) ∧ WF (KI.sin a) := by
  unfold Interval64.sin KI.sin
  simp only [toI, isNaN_toF ha.1, isNaN_toF ha.2]
  cases h : (isNaN a.lo || isNaN a.hi)
  · simp only [Bool.cond_false, Bool.false_eq_true, ite_false]
    simp only [Bool.or_eq_false_iff] at h
    simp only [toBits_toF_of_not_nan ha.1 h.1, toBits_toF_of_not_nan ha.2 h.2]
    have b1 := UInt64.toNat_lt (Trig.sinDownBits (UInt64.ofNat a.lo))
    have b2 := UInt64.toNat_lt (Trig.sinDownBits (UInt64.ofNat a.hi))
    have b3 := UInt64.toNat_lt (Trig.sinUpBits (UInt64.ofNat a.lo))
    have b4 := UInt64.toNat_lt (Trig.sinUpBits (UInt64.ofNat a.hi))
    have m1 : KI.minusOne < 2 ^ 64 := UInt64.toNat_lt _
    have p1 : KI.plusOne < 2 ^ 64 := UInt64.toNat_lt _
    generalize Spec.bitsToRat? (UInt64.ofNat a.lo) = qa
    generalize Spec.bitsToRat? (UInt64.ofNat a.hi) = qb
    rcases qa with _ | x <;> rcases qb with _ | y
    · exact ⟨by simp [minusOne_toF, plusOne_toF], m1, p1⟩
    · exact ⟨by simp [minusOne_toF, plusOne_toF], m1, p1⟩
    · exact ⟨by simp [minusOne_toF, plusOne_toF], m1, p1⟩
    · simp only [Directed.sinDown, Directed.sinUp, Directed.sinDownSpec, Directed.sinUpSpec,
        toBits_toF_of_not_nan ha.1 h.1, toBits_toF_of_not_nan ha.2 h.2, toF_ofBits]
      rw [fmin_toF b1 b2, fmax_toF b3 b4, minusOne_toF, plusOne_toF]
      refine ⟨?_, ?_, ?_⟩
      · cases Trig.avoids x y 3 <;> cases Trig.avoids x y 1 <;> rfl
      · cases Trig.avoids x y 3 <;> simp [fmin_lt b1 b2, m1]
      · cases Trig.avoids x y 1 <;> simp [fmax_lt b3 b4, p1]
  · simp only [Bool.cond_true, ite_true]; exact ⟨toI_invalid, wf_invalid⟩

theorem cos_toI {a : KI} (ha : WF a) : toI (KI.cos a) = Interval64.cos (toI a) ∧ WF (KI.cos a) := by
  unfold Interval64.cos KI.cos
  simp only [toI, isNaN_toF ha.1, isNaN_toF ha.2]
  cases h : (isNaN a.lo || isNaN a.hi)
  · simp only [Bool.cond_false, Bool.false_eq_true, ite_false]
    simp only [Bool.or_eq_false_iff] at h
    simp only [toBits_toF_of_not_nan ha.1 h.1, toBits_toF_of_not_nan ha.2 h.2]
    have b1 := UInt64.toNat_lt (Trig.cosDownBits (UInt64.ofNat a.lo))
    have b2 := UInt64.toNat_lt (Trig.cosDownBits (UInt64.ofNat a.hi))
    have b3 := UInt64.toNat_lt (Trig.cosUpBits (UInt64.ofNat a.lo))
    have b4 := UInt64.toNat_lt (Trig.cosUpBits (UInt64.ofNat a.hi))
    have m1 : KI.minusOne < 2 ^ 64 := UInt64.toNat_lt _
    have p1 : KI.plusOne < 2 ^ 64 := UInt64.toNat_lt _
    generalize Spec.bitsToRat? (UInt64.ofNat a.lo) = qa
    generalize Spec.bitsToRat? (UInt64.ofNat a.hi) = qb
    rcases qa with _ | x <;> rcases qb with _ | y
    · exact ⟨by simp [minusOne_toF, plusOne_toF], m1, p1⟩
    · exact ⟨by simp [minusOne_toF, plusOne_toF], m1, p1⟩
    · exact ⟨by simp [minusOne_toF, plusOne_toF], m1, p1⟩
    · simp only [Directed.cosDown, Directed.cosUp, Directed.cosDownSpec, Directed.cosUpSpec,
        toBits_toF_of_not_nan ha.1 h.1, toBits_toF_of_not_nan ha.2 h.2, toF_ofBits]
      rw [fmin_toF b1 b2, fmax_toF b3 b4, minusOne_toF, plusOne_toF]
      refine ⟨?_, ?_, ?_⟩
      · cases Trig.avoids x y 2 <;> cases Trig.avoids x y 0 <;> rfl
      · cases Trig.avoids x y 2 <;> simp [fmin_lt b1 b2, m1]
      · cases Trig.avoids x y 0 <;> simp [fmax_lt b3 b4, p1]
  · simp only [Bool.cond_true, ite_true]; exact ⟨toI_invalid, wf_invalid⟩

theorem ofRat_toI (q : Rat) : toI (KI.ofRat q) = ofRat q ∧ WF (KI.ofRat q) :=
  ⟨by simp only [toI, KI.ofRat, toF_toNat]; rfl, UInt64.toNat_lt _, UInt64.toNat_lt _⟩

theorem ofRatInterval_toI (lo hi : Rat) :
    toI (KI.ofRatInterval lo hi) = ofRatInterval lo hi ∧ WF (KI.ofRatInterval lo hi) :=
  ⟨by simp only [toI, KI.ofRatInterval, toF_toNat]; rfl, UInt64.toNat_lt _, UInt64.toNat_lt _⟩

end Interval64.KF
