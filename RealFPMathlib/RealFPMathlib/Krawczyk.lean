/-
Krawczyk-type certificates for square nonlinear systems `F₀ = … = F_{n-1} = 0` on a box `X`.

Certificate: a point `m ∈ X`, rational matrices `Y` (≈ `F'(m)⁻¹`) and `Z` (≈ `F'(m)`), a
rational `q < 1`, and the interval Jacobian `J` and `F(m)` enclosures (checked to equal what
`evalK` computes). With `G x = x - Y F(x)`, the checks give

* `G(X) ⊆ X` (the Krawczyk inclusion `m - Y F(m) + (I - Y J)(X - m) ⊆ X`),
* `‖G x - G y‖∞ ≤ q ‖x - y‖∞` on `X` (row sums of `I - Y J`),
* `Y` injective (`‖I - Z Y‖∞ ≤ q < 1`),

so `G` has a unique fixed point in `X` (Banach), which is the unique zero of `F` in `X`.
The Jacobian entries `aₖⱼ ∈ Jₖⱼ` appear as extra interval *variables* of an `IExpr`, so all
enclosures come from the existing `evalK` soundness theorem.
-/
import RealFPMathlib.Roots
import Mathlib.Data.List.GetD

open Interval64 Interval64.Spec Interval64.KF
open Interval64Proofs.FloatBits

noncomputable section

namespace RealFP.Roots

/-! ### Vectors as lists -/

/-- `[x 0, …, x (n-1)]`. -/
def vec (n : Nat) (x : Nat → ℝ) : List ℝ := (List.range n).map x

@[simp] theorem vec_length {n : Nat} {x : Nat → ℝ} : (vec n x).length = n := by simp [vec]

theorem vec_getD {n j : Nat} (x : Nat → ℝ) (h : j < n) : (vec n x).getD j 0 = x j := by
  simp [vec, List.getD_eq_getElem?_getD, h]

theorem vec_congr {n : Nat} {x y : Nat → ℝ} (h : ∀ j < n, x j = y j) : vec n x = vec n y := by
  simp only [vec]; apply List.map_congr_left; intro j hj; exact h j (List.mem_range.1 hj)

theorem eq_vec (xs : List ℝ) : xs = vec xs.length (fun j => xs.getD j 0) := by
  apply List.ext_getElem (by simp [vec]); intro j h1 h2
  simp [vec, List.getD_eq_getElem?_getD, h1]

theorem forall2_vec {β : Type} {R : ℝ → β → Prop} {N : Nat} {f : Nat → ℝ} {g : Nat → β}
    (h : ∀ t < N, R (f t) (g t)) : List.Forall₂ R (vec N f) ((List.range N).map g) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp [vec], fun i h1 h2 => ?_⟩
  simp only [vec, List.length_map, List.length_range] at h1
  simpa [vec] using h i h1

theorem inBoxes_iff {xs : List ℝ} {bs : List (ℚ × ℚ)} :
    InBoxes xs bs ↔ xs.length = bs.length ∧ ∀ j < bs.length,
      ((bs.getD j (0, 0)).1 : ℝ) ≤ xs.getD j 0 ∧ xs.getD j 0 ≤ ((bs.getD j (0, 0)).2 : ℝ) := by
  unfold InBoxes; rw [List.forall₂_iff_get]
  constructor
  · rintro ⟨hl, h⟩
    refine ⟨hl, fun j hj => ?_⟩
    have := h j (hl ▸ hj) hj
    simpa [List.getD_eq_getElem?_getD, hj, hl ▸ hj] using this
  · rintro ⟨hl, h⟩
    refine ⟨hl, fun j h1 h2 => ?_⟩
    have := h j h2
    simpa [List.getD_eq_getElem?_getD, h1, h2] using this

theorem inBoxes_vec {n : Nat} {x : Nat → ℝ} {bs : List (ℚ × ℚ)} (hn : bs.length = n) :
    InBoxes (vec n x) bs ↔ ∀ j < n,
      ((bs.getD j (0, 0)).1 : ℝ) ≤ x j ∧ x j ≤ ((bs.getD j (0, 0)).2 : ℝ) := by
  rw [inBoxes_iff]; subst hn
  constructor
  · rintro ⟨-, h⟩ j hj; have := h j hj; rwa [vec_getD x hj] at this
  · intro h; refine ⟨by simp, fun j hj => ?_⟩; rw [vec_getD x hj]; exact h j hj

/-! ### Sums as expressions -/

/-- `f 0 + (f 1 + … + (f (n-1) + 0))`. -/
def sumE (n : Nat) (f : Nat → IExpr) : IExpr := ((List.range n).map f).foldr IExpr.add (IExpr.rat 0)

theorem denote_foldr (xs : List ℝ) :
    ∀ l : List IExpr, (l.foldr IExpr.add (IExpr.rat 0)).denote xs = (l.map (·.denote xs)).sum
  | [] => by simp [IExpr.denote]
  | e :: l => by simp [IExpr.denote, denote_foldr xs l]

theorem lsum (n : Nat) (g : Nat → ℝ) : ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem denote_sumE (xs : List ℝ) (n : Nat) (f : Nat → IExpr) :
    (sumE n f).denote xs = ∑ i ∈ Finset.range n, (f i).denote xs := by
  rw [sumE, denote_foldr, List.map_map, lsum]; rfl

/-! ### Mean value theorem across a box (one coordinate at a time) -/

theorem set_vec {n r : Nat} (x : Nat → ℝ) (hr : r < n) (s : ℝ) :
    (vec n x).set r s = vec n (fun j => if j = r then s else x j) := by
  apply List.ext_getElem (by simp [vec]); intro j h1 h2
  simp only [List.getElem_set, vec, List.getElem_map, List.getElem_range]
  split_ifs with h h' h' <;> first | rfl | (subst h; exact absurd rfl h') | (exact absurd h'.symm h)

/-- `F x - F y = ∑ⱼ aⱼ (xⱼ - yⱼ)` with each `aⱼ` in the interval value of `∂ⱼF` on the box. -/
theorem mvt_box (F : IExpr) {bs : List (ℚ × ℚ)} {n : Nat} (hn : bs.length = n)
    (hd : domOK (boxes bs) F = true) {x y : Nat → ℝ}
    (hx : InBoxes (vec n x) bs) (hy : InBoxes (vec n y) bs) :
    ∃ a : Nat → ℝ, (∀ j < n, a j ∈ (toI (evalK (boxes bs) (F.deriv j))).toSet) ∧
      F.denote (vec n x) - F.denote (vec n y) = ∑ j ∈ Finset.range n, a j * (x j - y j) := by
  set X := boxes bs
  have hw : ∀ Q ∈ X, WF Q := boxes_wf bs
  let z : Nat → Nat → ℝ := fun r j => if j < r then x j else y j
  have hzb : ∀ r, InBoxes (vec n (z r)) bs := by
    intro r; rw [inBoxes_vec hn]; intro j hj
    have h1 := (inBoxes_vec hn).1 hx j hj; have h2 := (inBoxes_vec hn).1 hy j hj
    simp only [z]; split_ifs <;> assumption
  have hxm := boxes_mem hx
  have hym := boxes_mem hy
  have step : ∀ r < n, ∃ d, d ∈ (toI (evalK X (F.deriv r))).toSet ∧
      F.denote (vec n (z (r + 1))) - F.denote (vec n (z r)) = d * (x r - y r) := by
    intro r hr
    have hzm := boxes_mem (hzb r)
    have hxr : x r ∈ (toI (X.getD r zeroK)).toSet := by
      have := getD_mem_toI hxm r; rwa [vec_getD x hr] at this
    have hyr : y r ∈ (toI (X.getD r zeroK)).toSet := by
      have := getD_mem_toI hym r; rwa [vec_getD y hr] at this
    have hlen : r < (vec n (z r)).length := by simpa using hr
    obtain ⟨d, hdS, hmv⟩ := mvt_uIcc (S := fun d => d ∈ (toI (evalK X (F.deriv r))).toSet)
      (φ := fun s => F.denote ((vec n (z r)).set r s)) (a := y r) (b := x r) (fun t ht => by
        have htX := seg_mem hyr hxr ht
        exact ⟨_, (memK hw (forall2_setx hzm r htX) (F.deriv r)).1,
          hasDerivAt_box hw hzm hlen hd htX⟩)
    refine ⟨d, hdS, ?_⟩
    have e1 : (vec n (z r)).set r (x r) = vec n (z (r + 1)) := by
      rw [set_vec _ hr]; apply vec_congr; intro j hj
      simp only [z]; split_ifs <;> first | rfl | omega | (subst_vars; rfl)
    have e2 : (vec n (z r)).set r (y r) = vec n (z r) := by
      rw [set_vec _ hr]; apply vec_congr; intro j hj
      simp only [z]; split_ifs <;> first | rfl | omega | (subst_vars; rfl)
    simp only [e1, e2] at hmv
    exact hmv
  choose! a ha hstep using step
  refine ⟨a, ha, ?_⟩
  have hzn : vec n (z n) = vec n x := vec_congr fun j hj => by simp [z, hj]
  have hz0 : vec n (z 0) = vec n y := vec_congr fun j _ => by simp [z]
  rw [← hzn, ← hz0, ← Finset.sum_range_sub (fun r => F.denote (vec n (z r)))]
  exact Finset.sum_congr rfl fun r hr => hstep r (Finset.mem_range.1 hr)


/-! ### The Krawczyk check -/

/-- Entry `(i, k)` of a rational matrix given by rows (`0` outside). -/
def qget (Y : List (List ℚ)) (i k : Nat) : ℚ := (Y.getD i []).getD k 0

def delta (i j : Nat) : ℚ := if i = j then 1 else 0

/-- Variable layout of the Krawczyk expressions (`n` unknowns): `xⱼ` at `j`, `mⱼ` at `n + j`,
`bₖ = Fₖ(m)` at `2n + k`, `aₖⱼ ∈ ∂ⱼFₖ(X)` at `3n + (k n + j)`. -/
def xV (j : Nat) : IExpr := .var j
def mV (n j : Nat) : IExpr := .var (n + j)
def bV (n k : Nat) : IExpr := .var (2 * n + k)
def aV (n k j : Nat) : IExpr := .var (3 * n + (k * n + j))

/-- `δᵢⱼ - ∑ₖ Yᵢₖ aₖⱼ`. -/
def coefE (n : Nat) (Y : List (List ℚ)) (i j : Nat) : IExpr :=
  .sub (.rat (delta i j)) (sumE n fun k => .mul (.rat (qget Y i k)) (aV n k j))

/-- Row `i` of the Krawczyk operator `m - Y F(m) + (I - Y J)(x - m)`. -/
def kE (n : Nat) (Y : List (List ℚ)) (i : Nat) : IExpr :=
  .add (.sub (mV n i) (sumE n fun k => .mul (.rat (qget Y i k)) (bV n k)))
    (sumE n fun j => .mul (coefE n Y i j) (.sub (xV j) (mV n j)))

/-- Row `i` of `(I - Y J) d` (`d` in the unit box): its bound is the contraction factor. -/
def tE (n : Nat) (Y : List (List ℚ)) (i : Nat) : IExpr :=
  sumE n fun j => .mul (coefE n Y i j) (xV j)

/-- `(I - Z Y)ᵢⱼ`, exactly. -/
def nq (n : Nat) (Y Z : List (List ℚ)) (i j : Nat) : ℚ :=
  delta i j - ((List.range n).map fun k => qget Z i k * qget Y k j).sum

/-- Row `i` of `(I - Z Y) d`. -/
def nE (n : Nat) (Y Z : List (List ℚ)) (i : Nat) : IExpr :=
  sumE n fun j => .mul (.rat (nq n Y Z i j)) (xV j)

def ptBoxes (mq : List ℚ) : List (ℚ × ℚ) := mq.map fun c => (c, c)
def fget (Fs : List IExpr) (k : Nat) : IExpr := Fs.getD k (.rat 0)
/-- Enclosures of `Fₖ(m)`. -/
def bEnv (n : Nat) (Fs : List IExpr) (mq : List ℚ) : List KI :=
  (List.range n).map fun k => evalK (boxes (ptBoxes mq)) (fget Fs k)
/-- Interval Jacobian on the box, row-major. -/
def jEnv (n : Nat) (Fs : List IExpr) (bs : List (ℚ × ℚ)) : List KI :=
  (List.range (n * n)).map fun t => evalK (boxes bs) ((fget Fs (t / n)).deriv (t % n))
def unitBoxes (n : Nat) : List (ℚ × ℚ) := List.replicate n (-1, 1)

/-- The enclosure lies in `[-q, q]`. -/
def inQ (q : ℚ) (F : KI) : Bool := gLe (KI.ofRat q).lo F && gGe (KI.ofRat (-q)).hi F

/-- The enclosure lies in `[lo, hi]`. -/
def inLH (lo hi : ℚ) (F : KI) : Bool := gGe (KI.ofRat lo).hi F && gLe (KI.ofRat hi).lo F

/-- Krawczyk certificate (all found by native search; `B`, `J` are checked equal to `evalK`). -/
structure KCert where
  m : List ℚ
  Y : List (List ℚ)
  Z : List (List ℚ)
  q : ℚ
  B : List KI
  J : List KI

def rowOK (n : Nat) (bs : List (ℚ × ℚ)) (c : KCert) (env envT : List KI) (i : Nat) : Bool :=
  inLH (bs.getD i (0, 0)).1 (bs.getD i (0, 0)).2 (evalK env (kE n c.Y i)) &&
    inQ c.q (evalK envT (tE n c.Y i)) && inQ c.q (evalK envT (nE n c.Y c.Z i))

/-- **Krawczyk check** for `Fs = 0` on the box `bs`. -/
def krawCheck (Fs : List IExpr) (bs : List (ℚ × ℚ)) (c : KCert) : Bool :=
  Fs.length == bs.length && c.m.length == bs.length && decide (0 ≤ c.q) && decide (c.q < 1) &&
    (List.range bs.length).all (fun i =>
      decide ((bs.getD i (0, 0)).1 ≤ c.m.getD i 0 ∧ c.m.getD i 0 ≤ (bs.getD i (0, 0)).2)) &&
    Fs.all (domOK (boxes bs)) &&
    c.B == bEnv bs.length Fs c.m && c.J == jEnv bs.length Fs bs &&
    (List.range bs.length).all (rowOK bs.length bs c
      (boxes bs ++ boxes (ptBoxes c.m) ++ c.B ++ c.J)
      (boxes (unitBoxes bs.length) ++ boxes (ptBoxes c.m) ++ c.B ++ c.J))

/-! ### Soundness -/

theorem inQ_sound {q : ℚ} {F : KI} (hF : WF F) (h : inQ q F = true) {y : ℝ}
    (hy : y ∈ (toI F).toSet) : |y| ≤ q := by
  simp only [inQ, Bool.and_eq_true] at h
  have h1 := gLe_sound q F hF h.1 y hy
  have h2 := gGe_sound (-q) F hF h.2 y hy
  push_cast at h2
  exact abs_le.2 ⟨h2, h1⟩

theorem inLH_sound {lo hi : ℚ} {F : KI} (hF : WF F) (h : inLH lo hi F = true) {y : ℝ}
    (hy : y ∈ (toI F).toSet) : (lo : ℝ) ≤ y ∧ y ≤ hi := by
  simp only [inLH, Bool.and_eq_true] at h
  exact ⟨gGe_sound lo F hF h.1 y hy, gLe_sound hi F hF h.2 y hy⟩

theorem getD_app4 {n : Nat} (l1 l2 l3 l4 : List ℝ) (h1 : l1.length = n) (h2 : l2.length = n)
    (h3 : l3.length = n) :
    (∀ j < n, (l1 ++ l2 ++ l3 ++ l4).getD j 0 = l1.getD j 0) ∧
    (∀ j < n, (l1 ++ l2 ++ l3 ++ l4).getD (n + j) 0 = l2.getD j 0) ∧
    (∀ k < n, (l1 ++ l2 ++ l3 ++ l4).getD (2 * n + k) 0 = l3.getD k 0) ∧
    (∀ t, (l1 ++ l2 ++ l3 ++ l4).getD (3 * n + t) 0 = l4.getD t 0) := by
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun k hk => ?_, fun t => ?_⟩
  · rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega),
      List.getD_append _ _ _ _ (by omega)]
  · rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega),
      List.getD_append_right _ _ _ _ (by omega)]
    congr 1; omega
  · rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega)]
    congr 1; simp; omega
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    congr 1; simp; omega

theorem wf_app {l1 l2 : List KI} (h1 : ∀ X ∈ l1, WF X) (h2 : ∀ X ∈ l2, WF X) :
    ∀ X ∈ l1 ++ l2, WF X := fun X hX => (List.mem_append.1 hX).elim (h1 X) (h2 X)

theorem wf_map {β : Type} (l : List β) (f : β → KI)
    (hf : ∀ b, WF (f b)) : ∀ X ∈ l.map f, WF X := by
  intro X hX; obtain ⟨b, -, rfl⟩ := List.mem_map.1 hX; exact hf b

theorem lsumQ (n : Nat) (g : Nat → ℚ) :
    ((((List.range n).map g).sum : ℚ) : ℝ) = ∑ i ∈ Finset.range n, (g i : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Rat.cast_add, ih, Finset.sum_range_succ]
    simp

theorem delta_cast (i j : Nat) : ((delta i j : ℚ) : ℝ) = if i = j then 1 else 0 := by
  unfold delta; split_ifs <;> simp

theorem sum_delta {n i : Nat} (hi : i < n) (d : Nat → ℝ) :
    ∑ j ∈ Finset.range n, (if i = j then (1 : ℝ) else 0) * d j = d i := by
  simp [Finset.mem_range.2 hi]

section Sound

variable {Fs : List IExpr} {bs : List (ℚ × ℚ)} {c : KCert}

/-- Everything the check gives, unpacked. -/
structure Facts (Fs : List IExpr) (bs : List (ℚ × ℚ)) (c : KCert) : Prop where
  hF : Fs.length = bs.length
  hm : c.m.length = bs.length
  hq0 : 0 ≤ c.q
  hq1 : c.q < 1
  hmb : ∀ i < bs.length, (bs.getD i (0, 0)).1 ≤ c.m.getD i 0 ∧ c.m.getD i 0 ≤ (bs.getD i (0, 0)).2
  hdom : ∀ k, domOK (boxes bs) (fget Fs k) = true
  hB : c.B = bEnv bs.length Fs c.m
  hJ : c.J = jEnv bs.length Fs bs
  hrow : ∀ i < bs.length, rowOK bs.length bs c
      (boxes bs ++ boxes (ptBoxes c.m) ++ c.B ++ c.J)
      (boxes (unitBoxes bs.length) ++ boxes (ptBoxes c.m) ++ c.B ++ c.J) i = true

theorem facts_of_check (h : krawCheck Fs bs c = true) : Facts Fs bs c := by
  simp only [krawCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hF, hm⟩, hq0⟩, hq1⟩, hmb⟩, hdom⟩, hB⟩, hJ⟩, hrow⟩ := h
  refine ⟨hF, hm, hq0, hq1, hmb, fun k => ?_, hB, hJ, hrow⟩
  unfold fget
  by_cases hk : k < Fs.length
  · rw [List.getD_eq_getElem _ _ hk]; exact hdom _ (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ (by omega)]; rfl


/-- Real centre. -/
def mR (c : KCert) (j : Nat) : ℝ := (c.m.getD j 0 : ℝ)
/-- `Fₖ` at a vector. -/
def Fk (Fs : List IExpr) (n k : Nat) (x : Nat → ℝ) : ℝ := (fget Fs k).denote (vec n x)
/-- `G x = x - Y F(x)`. -/
def Gv (Fs : List IExpr) (n : Nat) (Y : List (List ℚ)) (x : Nat → ℝ) (i : Nat) : ℝ :=
  x i - ∑ k ∈ Finset.range n, (qget Y i k : ℝ) * Fk Fs n k x

theorem kraw_alg {n i : Nat} (hi : i < n) (Y : Nat → Nat → ℝ) (x m Fx Fm : Nat → ℝ)
    (a : Nat → Nat → ℝ) (heq : ∀ k, Fx k - Fm k = ∑ j ∈ Finset.range n, a k j * (x j - m j)) :
    x i - ∑ k ∈ Finset.range n, Y i k * Fx k = m i - ∑ k ∈ Finset.range n, Y i k * Fm k +
      ∑ j ∈ Finset.range n, ((if i = j then 1 else 0) - ∑ k ∈ Finset.range n, Y i k * a k j) *
        (x j - m j) := by
  have h1 : ∑ k ∈ Finset.range n, Y i k * Fx k = ∑ k ∈ Finset.range n, Y i k * Fm k +
      ∑ k ∈ Finset.range n, Y i k * ∑ j ∈ Finset.range n, a k j * (x j - m j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← heq k]; ring
  have h2 : ∑ j ∈ Finset.range n, ((if i = j then 1 else 0) - ∑ k ∈ Finset.range n, Y i k * a k j) *
      (x j - m j) = (x i - m i) -
      ∑ k ∈ Finset.range n, Y i k * ∑ j ∈ Finset.range n, a k j * (x j - m j) := by
    simp only [sub_mul, Finset.sum_sub_distrib, sum_delta hi, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h1, h2]; ring

section Layout

variable {n : Nat} {L : List ℝ} {w m Fm : Nat → ℝ} {a : Nat → Nat → ℝ}

/-- Values of the layout variables in a list. -/
structure Lay (n : Nat) (L : List ℝ) (w m Fm : Nat → ℝ) (a : Nat → Nat → ℝ) : Prop where
  dx : ∀ j < n, L.getD j 0 = w j
  dm : ∀ j < n, L.getD (n + j) 0 = m j
  db : ∀ k < n, L.getD (2 * n + k) 0 = Fm k
  da : ∀ k < n, ∀ j < n, L.getD (3 * n + (k * n + j)) 0 = a k j

theorem div_mod_aux {n k j : Nat} (hj : j < n) : (k * n + j) / n = k ∧ (k * n + j) % n = j := by
  have hn : 0 < n := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hj, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

theorem lay_mk (n : Nat) (w m Fm : Nat → ℝ) (a : Nat → Nat → ℝ) :
    Lay n (vec n w ++ vec n m ++ vec n Fm ++ vec (n * n) (fun t => a (t / n) (t % n))) w m Fm a := by
  have h4 := getD_app4 (vec n w) (vec n m) (vec n Fm) (vec (n * n) (fun t => a (t / n) (t % n)))
    vec_length vec_length vec_length
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun k hk => ?_, fun k hk j hj => ?_⟩
  · rw [h4.1 j hj, vec_getD _ hj]
  · rw [h4.2.1 j hj, vec_getD _ hj]
  · rw [h4.2.2.1 k hk, vec_getD _ hk]
  · have hlt : k * n + j < n * n := by nlinarith
    rw [h4.2.2.2, vec_getD _ hlt, (div_mod_aux hj).1, (div_mod_aux hj).2]

theorem coef_denote (hL : Lay n L w m Fm a) (Y : List (List ℚ)) (i : Nat) {j : Nat} (hj : j < n) :
    (coefE n Y i j).denote L =
      (if i = j then 1 else 0) - ∑ k ∈ Finset.range n, (qget Y i k : ℝ) * a k j := by
  simp only [coefE, IExpr.denote, denote_sumE, aV, delta_cast]
  congr 1
  exact Finset.sum_congr rfl fun k hk => by rw [hL.da k (Finset.mem_range.1 hk) j hj]

theorem kE_denote (hL : Lay n L w m Fm a) (Y : List (List ℚ)) {i : Nat} (hi : i < n) :
    (kE n Y i).denote L = m i - ∑ k ∈ Finset.range n, (qget Y i k : ℝ) * Fm k +
      ∑ j ∈ Finset.range n, ((if i = j then 1 else 0) -
        ∑ k ∈ Finset.range n, (qget Y i k : ℝ) * a k j) * (w j - m j) := by
  simp only [kE, IExpr.denote, denote_sumE, mV, bV, xV]
  rw [hL.dm i hi]
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun k hk => by rw [hL.db k (Finset.mem_range.1 hk)]
  · exact Finset.sum_congr rfl fun j hj => by
      have hj' := Finset.mem_range.1 hj
      rw [coef_denote hL Y i hj', hL.dx j hj', hL.dm j hj']

theorem tE_denote (hL : Lay n L w m Fm a) (Y : List (List ℚ)) (i : Nat) :
    (tE n Y i).denote L = ∑ j ∈ Finset.range n, ((if i = j then 1 else 0) -
        ∑ k ∈ Finset.range n, (qget Y i k : ℝ) * a k j) * w j := by
  simp only [tE, denote_sumE, IExpr.denote, xV]
  exact Finset.sum_congr rfl fun j hj => by
    have hj' := Finset.mem_range.1 hj
    rw [coef_denote hL Y i hj', hL.dx j hj']

theorem nE_denote (hL : Lay n L w m Fm a) (Y Z : List (List ℚ)) (i : Nat) :
    (nE n Y Z i).denote L = ∑ j ∈ Finset.range n, ((if i = j then 1 else 0) -
        ∑ k ∈ Finset.range n, (qget Z i k : ℝ) * qget Y k j) * w j := by
  simp only [nE, denote_sumE, IExpr.denote, xV]
  exact Finset.sum_congr rfl fun j hj => by
    have hj' := Finset.mem_range.1 hj
    rw [hL.dx j hj', nq, Rat.cast_sub, delta_cast, lsumQ]
    push_cast; rfl

end Layout

variable {Fs : List IExpr} {bs : List (ℚ × ℚ)} {c : KCert}

theorem ptBoxes_getD (mq : List ℚ) (j : Nat) : (ptBoxes mq).getD j (0, 0) = (mq.getD j 0, mq.getD j 0) := by
  show (mq.map fun c => (c, c)).getD j ((fun c : ℚ => (c, c)) 0) = _
  rw [List.getD_map]

theorem inBoxes_m (hf : Facts Fs bs c) : InBoxes (vec bs.length (mR c)) (ptBoxes c.m) := by
  rw [inBoxes_vec (by simp [ptBoxes, hf.hm])]
  intro j _; rw [ptBoxes_getD]; exact ⟨le_rfl, le_rfl⟩

theorem inBoxes_m' (hf : Facts Fs bs c) : InBoxes (vec bs.length (mR c)) bs := by
  rw [inBoxes_vec rfl]
  intro j hj; have := hf.hmb j hj
  exact ⟨by simp only [mR]; exact_mod_cast this.1, by simp only [mR]; exact_mod_cast this.2⟩

theorem env_mem (hf : Facts Fs bs c) {l0 : List ℝ} {E0 : List KI}
    (h0 : List.Forall₂ (fun x X => x ∈ (toI X).toSet) l0 E0) {a : Nat → Nat → ℝ}
    (ha : ∀ k < bs.length, ∀ j < bs.length,
      a k j ∈ (toI (evalK (boxes bs) ((fget Fs k).deriv j))).toSet) :
    List.Forall₂ (fun x X => x ∈ (toI X).toSet)
      (l0 ++ vec bs.length (mR c) ++ vec bs.length (fun k => Fk Fs bs.length k (mR c)) ++
        vec (bs.length * bs.length) (fun t => a (t / bs.length) (t % bs.length)))
      (E0 ++ boxes (ptBoxes c.m) ++ c.B ++ c.J) := by
  have hM := boxes_mem (inBoxes_m hf)
  refine List.rel_append (List.rel_append (List.rel_append h0 hM) ?_) ?_
  · rw [hf.hB]
    exact forall2_vec fun k _ => (memK (boxes_wf _) hM (fget Fs k)).1
  · rw [hf.hJ]
    refine forall2_vec fun t ht => ?_
    have hn : 0 < bs.length := by
      rcases Nat.eq_zero_or_pos bs.length with h | h
      · simp [h] at ht
      · exact h
    exact ha _ (Nat.div_lt_of_lt_mul ht) _ (Nat.mod_lt _ hn)

theorem env_wf (hf : Facts Fs bs c) {E0 : List KI} (h0 : ∀ X ∈ E0, WF X) :
    ∀ X ∈ E0 ++ boxes (ptBoxes c.m) ++ c.B ++ c.J, WF X := by
  refine wf_app (wf_app (wf_app h0 (boxes_wf _)) ?_) ?_
  · rw [hf.hB]; exact wf_map _ _ fun k => (evalK_toI (boxes_wf _) _).2
  · rw [hf.hJ]; exact wf_map _ _ fun t => (evalK_toI (boxes_wf _) _).2

/-- Derivative values between two points of the box, for every `Fₖ`. -/
theorem mvt_all (hf : Facts Fs bs c) {x y : Nat → ℝ} (hx : InBoxes (vec bs.length x) bs)
    (hy : InBoxes (vec bs.length y) bs) :
    ∃ a : Nat → Nat → ℝ, (∀ k < bs.length, ∀ j < bs.length,
      a k j ∈ (toI (evalK (boxes bs) ((fget Fs k).deriv j))).toSet) ∧
      ∀ k, Fk Fs bs.length k x - Fk Fs bs.length k y =
        ∑ j ∈ Finset.range bs.length, a k j * (x j - y j) := by
  have := fun k => mvt_box (fget Fs k) rfl (hf.hdom k) hx hy
  choose a ha heq using this
  exact ⟨a, fun k _ j hj => ha k j hj, heq⟩

/-- **Inclusion**: `G` maps the box into itself. -/
theorem maps_into (hf : Facts Fs bs c) {x : Nat → ℝ} (hx : InBoxes (vec bs.length x) bs) :
    ∀ i < bs.length, ((bs.getD i (0, 0)).1 : ℝ) ≤ Gv Fs bs.length c.Y x i ∧
      Gv Fs bs.length c.Y x i ≤ ((bs.getD i (0, 0)).2 : ℝ) := by
  obtain ⟨a, ha, heq⟩ := mvt_all hf hx (inBoxes_m' hf)
  have hL := env_mem hf (boxes_mem hx) ha
  have hW := env_wf hf (boxes_wf bs)
  have hlay := lay_mk bs.length x (mR c) (fun k => Fk Fs bs.length k (mR c)) a
  intro i hi
  have hrow := hf.hrow i hi
  simp only [rowOK, Bool.and_eq_true] at hrow
  have hm := memK hW hL (kE bs.length c.Y i)
  have hK := inLH_sound hm.2 hrow.1.1 hm.1
  rw [kE_denote hlay c.Y hi] at hK
  have e := kraw_alg hi (fun i k => (qget c.Y i k : ℝ)) x (mR c) (fun k => Fk Fs bs.length k x)
    (fun k => Fk Fs bs.length k (mR c)) a heq
  rw [Gv, e]; exact hK

/-- **Contraction** in the sup norm. -/
theorem lip (hf : Facts Fs bs c) {x y : Nat → ℝ} (hx : InBoxes (vec bs.length x) bs)
    (hy : InBoxes (vec bs.length y) bs) {t : ℝ} (ht : 0 ≤ t)
    (hxy : ∀ j < bs.length, |x j - y j| ≤ t) :
    ∀ i < bs.length, |Gv Fs bs.length c.Y x i - Gv Fs bs.length c.Y y i| ≤ c.q * t := by
  intro i hi
  rcases ht.lt_or_eq with htp | ht0
  · obtain ⟨a, ha, heq⟩ := mvt_all hf hx hy
    let d : Nat → ℝ := fun j => (x j - y j) / t
    have hd : InBoxes (vec bs.length d) (unitBoxes bs.length) := by
      rw [inBoxes_vec (by simp [unitBoxes])]
      intro j hj
      have h1 : (unitBoxes bs.length).getD j (0, 0) = (-1, 1) := by
        simp [unitBoxes, List.getD_eq_getElem?_getD, hj]
      rw [h1]
      have : |(x j - y j) / t| ≤ 1 := by
        rw [abs_div, abs_of_pos htp]; exact (div_le_one htp).2 (hxy j hj)
      simp only [d]; push_cast; exact abs_le.1 this
    have hL := env_mem hf (boxes_mem hd) (a := fun k j => a k j) (fun k hk j hj => by
      have := ha k hk j hj; exact this)
    have hW := env_wf hf (boxes_wf (unitBoxes bs.length))
    have hlay := lay_mk bs.length d (mR c) (fun k => Fk Fs bs.length k (mR c)) a
    have hrow := hf.hrow i hi
    simp only [rowOK, Bool.and_eq_true] at hrow
    have hm := memK hW hL (tE bs.length c.Y i)
    have hT := inQ_sound hm.2 hrow.1.2 hm.1
    rw [tE_denote hlay c.Y i] at hT
    have e := kraw_alg hi (fun i k => (qget c.Y i k : ℝ)) x y (fun k => Fk Fs bs.length k x)
      (fun k => Fk Fs bs.length k y) a heq
    have e2 : Gv Fs bs.length c.Y x i - Gv Fs bs.length c.Y y i = t *
        ∑ j ∈ Finset.range bs.length, ((if i = j then 1 else 0) -
          ∑ k ∈ Finset.range bs.length, (qget c.Y i k : ℝ) * a k j) * d j := by
      rw [Gv, Gv, e, Finset.mul_sum]
      have : ∀ j ∈ Finset.range bs.length, t * (((if i = j then 1 else 0) -
          ∑ k ∈ Finset.range bs.length, (qget c.Y i k : ℝ) * a k j) * d j) =
          ((if i = j then 1 else 0) - ∑ k ∈ Finset.range bs.length, (qget c.Y i k : ℝ) * a k j) *
            (x j - y j) := fun j _ => by simp only [d]; field_simp
      rw [Finset.sum_congr rfl this]; ring
    rw [e2, abs_mul, abs_of_pos htp, mul_comm]
    exact mul_le_mul_of_nonneg_right hT htp.le
  · subst ht0
    have hv : vec bs.length x = vec bs.length y :=
      vec_congr fun j hj => by have := hxy j hj; rw [abs_nonpos_iff, sub_eq_zero] at this; exact this
    have hxi : x i = y i := by have := hxy i hi; rw [abs_nonpos_iff, sub_eq_zero] at this; exact this
    simp only [Gv, Fk, hv, hxi, sub_self, abs_zero, mul_zero, le_refl]

/-- **`Y` is injective** (from `‖I - Z Y‖ ≤ q < 1`). -/
theorem y_inj (hf : Facts Fs bs c) {u : Nat → ℝ}
    (hu : ∀ k < bs.length, ∑ j ∈ Finset.range bs.length, (qget c.Y k j : ℝ) * u j = 0) :
    ∀ j < bs.length, u j = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨j0, hj0, hu0⟩ := hne
  obtain ⟨jm, hjm, hmax⟩ := Finset.exists_max_image (Finset.range bs.length) (fun j => |u j|)
    ⟨j0, Finset.mem_range.2 hj0⟩
  have hjm' := Finset.mem_range.1 hjm
  have htp : 0 < |u jm| := lt_of_lt_of_le (abs_pos.2 hu0) (hmax j0 (Finset.mem_range.2 hj0))
  set t := |u jm|
  let d : Nat → ℝ := fun j => u j / t
  have hd : InBoxes (vec bs.length d) (unitBoxes bs.length) := by
    rw [inBoxes_vec (by simp [unitBoxes])]
    intro j hj
    have h1 : (unitBoxes bs.length).getD j (0, 0) = (-1, 1) := by
      simp [unitBoxes, List.getD_eq_getElem?_getD, hj]
    rw [h1]
    have : |u j / t| ≤ 1 := by
      rw [abs_div, abs_of_pos htp]; exact (div_le_one htp).2 (hmax j (Finset.mem_range.2 hj))
    simp only [d]; push_cast; exact abs_le.1 this
  obtain ⟨a, ha, -⟩ := mvt_all hf (inBoxes_m' hf) (inBoxes_m' hf)
  have hL := env_mem hf (boxes_mem hd) ha
  have hW := env_wf hf (boxes_wf (unitBoxes bs.length))
  have hlay := lay_mk bs.length d (mR c) (fun k => Fk Fs bs.length k (mR c)) a
  have hrow := hf.hrow jm hjm'
  simp only [rowOK, Bool.and_eq_true] at hrow
  have hm := memK hW hL (nE bs.length c.Y c.Z jm)
  have hN := inQ_sound hm.2 hrow.2 hm.1
  rw [nE_denote hlay c.Y c.Z jm] at hN
  have hYd : ∀ k ∈ Finset.range bs.length,
      ∑ j ∈ Finset.range bs.length, (qget c.Y k j : ℝ) * d j = 0 := fun k hk => by
    simp only [d, mul_div_assoc', ← Finset.sum_div, hu k (Finset.mem_range.1 hk), zero_div]
  have e : ∑ j ∈ Finset.range bs.length, ((if jm = j then 1 else 0) -
      ∑ k ∈ Finset.range bs.length, (qget c.Z jm k : ℝ) * qget c.Y k j) * d j = d jm := by
    simp only [sub_mul, Finset.sum_sub_distrib, sum_delta hjm', Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ k ∈ Finset.range bs.length, ∑ j ∈ Finset.range bs.length,
        (qget c.Z jm k : ℝ) * qget c.Y k j * d j = 0 := fun k hk => by
      simp only [mul_assoc, ← Finset.mul_sum, hYd k hk, mul_zero]
    rw [Finset.sum_eq_zero this, sub_zero]
  rw [e] at hN
  have h1 : |d jm| = 1 := by simp only [d]; rw [abs_div, abs_of_pos htp]; exact div_self htp.ne'
  rw [h1] at hN
  have := hf.hq1
  have : (c.q : ℝ) < 1 := by exact_mod_cast this
  linarith


theorem allZero_iff (hF : Fs.length = bs.length) {xs : List ℝ} :
    AllZero Fs xs ↔ ∀ k < bs.length, (fget Fs k).denote xs = 0 := by
  constructor
  · intro h k hk; unfold fget; rw [List.getD_eq_getElem _ _ (by omega)]
    exact h _ (List.getElem_mem _)
  · intro h e he
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
    have := h k (by omega); unfold fget at this; rwa [List.getD_eq_getElem _ _ hk] at this

/-- Fixed points of `G` are zeros of `F`. -/
theorem zero_of_fixed (hf : Facts Fs bs c) {x : Nat → ℝ}
    (hfix : ∀ i < bs.length, Gv Fs bs.length c.Y x i = x i) :
    ∀ k < bs.length, Fk Fs bs.length k x = 0 :=
  y_inj hf (u := fun k => Fk Fs bs.length k x) fun i hi => by
    have := hfix i hi; simp only [Gv] at this; linarith

/-- **Existence** (Banach fixed point theorem on the box). -/
theorem kraw_exists (h : krawCheck Fs bs c = true) : ∃ xs, InBoxes xs bs ∧ AllZero Fs xs := by
  have hf := facts_of_check h
  let n := bs.length
  let toN : (Fin n → ℝ) → ℕ → ℝ := fun v j => if hj : j < n then v ⟨j, hj⟩ else 0
  let lo : Fin n → ℝ := fun i => ((bs.getD i (0, 0)).1 : ℝ)
  let hi : Fin n → ℝ := fun i => ((bs.getD i (0, 0)).2 : ℝ)
  let S : Set (Fin n → ℝ) := {v | ∀ i, lo i ≤ v i ∧ v i ≤ hi i}
  have hmem : ∀ v, v ∈ S ↔ InBoxes (vec n (toN v)) bs := by
    intro v; rw [inBoxes_vec rfl]
    constructor
    · intro hv j hj; rw [show toN v j = v ⟨j, hj⟩ from dif_pos hj]; exact hv ⟨j, hj⟩
    · intro hv i; have := hv i i.2; simp only [toN, i.2, ↓reduceDIte] at this; exact this
  have hS : IsClosed S := by
    have : S = ⋂ i : Fin n, ({v : Fin n → ℝ | lo i ≤ v i} ∩ {v | v i ≤ hi i}) := by
      ext v; simp [S]
    rw [this]
    exact isClosed_iInter fun i => (isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_le (continuous_apply i) continuous_const)
  have : CompleteSpace S := hS.completeSpace_coe
  have hm0 : (fun i : Fin n => mR c i) ∈ S := by
    rw [hmem]
    have : vec n (toN fun i : Fin n => mR c i) = vec n (mR c) :=
      vec_congr fun j hj => by simp [toN, hj]
    rw [this]; exact inBoxes_m' hf
  have : Nonempty S := ⟨⟨_, hm0⟩⟩
  let Gf : (Fin n → ℝ) → Fin n → ℝ := fun v i => Gv Fs n c.Y (toN v) i
  have hmaps : ∀ v ∈ S, Gf v ∈ S := fun v hv i => maps_into hf ((hmem v).1 hv) i i.2
  let f : S → S := fun v => ⟨Gf v.1, hmaps v.1 v.2⟩
  have hq0 : (0 : ℝ) ≤ c.q := by exact_mod_cast hf.hq0
  have hK : ContractingWith (Real.toNNReal c.q) f := by
    refine ⟨by rw [Real.toNNReal_lt_one]; exact_mod_cast hf.hq1,
      LipschitzWith.of_dist_le_mul fun v w => ?_⟩
    rw [Real.coe_toNNReal _ hq0, Subtype.dist_eq, Subtype.dist_eq]
    refine (dist_pi_le_iff (mul_nonneg hq0 dist_nonneg)).2 fun i => ?_
    rw [Real.dist_eq]
    refine lip hf ((hmem _).1 v.2) ((hmem _).1 w.2) dist_nonneg (fun j hj => ?_) i i.2
    rw [show toN v.1 j = v.1 ⟨j, hj⟩ from dif_pos hj, show toN w.1 j = w.1 ⟨j, hj⟩ from dif_pos hj]
    rw [← Real.dist_eq]; exact dist_le_pi_dist v.1 w.1 ⟨j, hj⟩
  have hp := ContractingWith.fixedPoint_isFixedPt (f := f) hK
  set p := ContractingWith.fixedPoint f hK
  have hfix : ∀ i < n, Gv Fs n c.Y (toN p.1) i = toN p.1 i := by
    intro i hi
    have := congrFun (congrArg Subtype.val hp) ⟨i, hi⟩
    simp only [toN, hi, ↓reduceDIte]; exact this
  have hz := zero_of_fixed hf hfix
  refine ⟨vec n (toN p.1), (hmem _).1 p.2, (allZero_iff hf.hF).2 fun k hk => hz k hk⟩

/-- **Uniqueness**: two zeros in the box coincide (`G` is a contraction). -/
theorem kraw_unique (h : krawCheck Fs bs c = true) {xs ys : List ℝ} (hx : InBoxes xs bs)
    (hzx : AllZero Fs xs) (hy : InBoxes ys bs) (hzy : AllZero Fs ys) : xs = ys := by
  have hf := facts_of_check h
  have lx : xs.length = bs.length := List.Forall₂.length_eq hx
  have ly : ys.length = bs.length := List.Forall₂.length_eq hy
  let x : Nat → ℝ := fun j => xs.getD j 0
  let y : Nat → ℝ := fun j => ys.getD j 0
  have ex : xs = vec bs.length x := by conv_lhs => rw [eq_vec xs]
                                       rw [lx]
  have ey : ys = vec bs.length y := by conv_lhs => rw [eq_vec ys]
                                       rw [ly]
  rw [ex] at hx hzx ⊢; rw [ey] at hy hzy ⊢
  have fx : ∀ i < bs.length, Gv Fs bs.length c.Y x i = x i := fun i _ => by
    have hz : ∀ k ∈ Finset.range bs.length, (qget c.Y i k : ℝ) * Fk Fs bs.length k x = 0 :=
      fun k hk => by rw [Fk, (allZero_iff hf.hF).1 hzx k (Finset.mem_range.1 hk), mul_zero]
    simp only [Gv, Finset.sum_eq_zero hz, sub_zero]
  have fy : ∀ i < bs.length, Gv Fs bs.length c.Y y i = y i := fun i _ => by
    have hz : ∀ k ∈ Finset.range bs.length, (qget c.Y i k : ℝ) * Fk Fs bs.length k y = 0 :=
      fun k hk => by rw [Fk, (allZero_iff hf.hF).1 hzy k (Finset.mem_range.1 hk), mul_zero]
    simp only [Gv, Finset.sum_eq_zero hz, sub_zero]
  apply vec_congr
  intro j hj
  obtain ⟨jm, hjm, hmax⟩ := Finset.exists_max_image (Finset.range bs.length) (fun j => |x j - y j|)
    ⟨j, Finset.mem_range.2 hj⟩
  have hjm' := Finset.mem_range.1 hjm
  have hl := lip hf hx hy (abs_nonneg (x jm - y jm))
    (fun j hj => hmax j (Finset.mem_range.2 hj)) jm hjm'
  rw [fx jm hjm', fy jm hjm'] at hl
  have hq1 : (c.q : ℝ) < 1 := by exact_mod_cast hf.hq1
  have h0 : |x jm - y jm| = 0 := by
    have := abs_nonneg (x jm - y jm); nlinarith
  have := hmax j (Finset.mem_range.2 hj)
  rw [h0, abs_nonpos_iff, sub_eq_zero] at this
  exact this

end Sound

/-! ### Statements over a type of points -/

theorem existsUnique_of {T : Type} (toL : T → List ℝ) (ofL : List ℝ → T) (P : List ℝ → Prop)
    (n : Nat) (hlen : ∀ xs, P xs → xs.length = n) (hto : ∀ xs, xs.length = n → toL (ofL xs) = xs)
    (hinj : ∀ p q, toL p = toL q → p = q) (hex : ∃ xs, P xs)
    (hu : ∀ xs ys, P xs → P ys → xs = ys) : ∃! p : T, P (toL p) := by
  obtain ⟨xs, hxs⟩ := hex
  have e := hto xs (hlen xs hxs)
  refine ⟨ofL xs, by show P (toL (ofL xs)); rw [e]; exact hxs, fun p hp => hinj _ _ ?_⟩
  rw [e]; exact hu _ _ hp hxs

/-- **Krawczyk, existence and uniqueness** for points of any type `T` with a coordinate list. -/
theorem kraw_existsUnique {T : Type} (Fs : List IExpr) (bs : List (ℚ × ℚ)) (c : KCert)
    (toL : T → List ℝ) (ofL : List ℝ → T) (hto : ∀ xs, xs.length = bs.length → toL (ofL xs) = xs)
    (hinj : ∀ p q, toL p = toL q → p = q) (h : krawCheck Fs bs c = true) :
    ∃! p : T, InBoxes (toL p) bs ∧ AllZero Fs (toL p) :=
  existsUnique_of toL ofL (fun xs => InBoxes xs bs ∧ AllZero Fs xs) bs.length
    (fun _ h => List.Forall₂.length_eq h.1) hto hinj (kraw_exists h)
    (fun _ _ h1 h2 => kraw_unique h h1.1 h1.2 h2.1 h2.2)

/-- **Krawczyk, existence** only. -/
theorem kraw_exists' {T : Type} (Fs : List IExpr) (bs : List (ℚ × ℚ)) (c : KCert)
    (toL : T → List ℝ) (ofL : List ℝ → T) (hto : ∀ xs, xs.length = bs.length → toL (ofL xs) = xs)
    (h : krawCheck Fs bs c = true) : ∃ p : T, InBoxes (toL p) bs ∧ AllZero Fs (toL p) := by
  obtain ⟨xs, h1, h2⟩ := kraw_exists h
  have e := hto xs (List.Forall₂.length_eq h1)
  exact ⟨ofL xs, by rw [e]; exact ⟨h1, h2⟩⟩

/-! Coordinate lists for `ℝ`, `ℝ × ℝ`, `ℝ × ℝ × ℝ` and `Fin n → ℝ`. -/

theorem coords1_to (xs : List ℝ) (h : xs.length = 1) : [xs.getD 0 0] = xs := by
  match xs, h with | [_], _ => rfl
theorem coords1_inj (p q : ℝ) (h : [p] = [q]) : p = q := by simpa using h

theorem coords2_to (xs : List ℝ) (h : xs.length = 2) :
    [(xs.getD 0 0, xs.getD 1 0).1, (xs.getD 0 0, xs.getD 1 0).2] = xs := by
  match xs, h with | [_, _], _ => rfl
theorem coords2_inj (p q : ℝ × ℝ) (h : [p.1, p.2] = [q.1, q.2]) : p = q := by
  simp only [List.cons.injEq, and_true] at h; exact Prod.ext h.1 h.2

theorem coords3_to (xs : List ℝ) (h : xs.length = 3) :
    [(xs.getD 0 0, xs.getD 1 0, xs.getD 2 0).1, (xs.getD 0 0, xs.getD 1 0, xs.getD 2 0).2.1,
      (xs.getD 0 0, xs.getD 1 0, xs.getD 2 0).2.2] = xs := by
  match xs, h with | [_, _, _], _ => rfl
theorem coords3_inj (p q : ℝ × ℝ × ℝ) (h : [p.1, p.2.1, p.2.2] = [q.1, q.2.1, q.2.2]) : p = q := by
  simp only [List.cons.injEq, and_true] at h; exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)

theorem coordsFin_to (n : Nat) (xs : List ℝ) (h : xs.length = n) :
    List.ofFn (fun i : Fin n => xs.getD i 0) = xs := by
  apply List.ext_getElem (by simp [h]); intro j h1 h2
  simp [List.getD_eq_getElem?_getD, h2]
theorem coordsFin_inj (n : Nat) (p q : Fin n → ℝ) (h : List.ofFn p = List.ofFn q) : p = q :=
  List.ofFn_injective h

end RealFP.Roots
