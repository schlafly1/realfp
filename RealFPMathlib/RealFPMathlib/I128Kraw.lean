/-
Krawczyk certificates for square systems at precision 128 (mirror of `Krawczyk.lean` with the
dyadic evaluator `Interval128.Dy.evalQ`). The expressions (`kE`, `tE`, `nE`), the variable layout
and the algebra are shared with the 64-bit version; only the enclosures change.

The certificate is a centre `m` and rational matrices `Y ≈ F'(m)⁻¹`, `Z ≈ F'(m)` and a bound
`q < 1`; the enclosures of `F(m)` and of the interval Jacobian are recomputed by the check.
-/
import RealFPMathlib.I128Roots
import RealFPMathlib.Krawczyk

open Interval64 Interval64.KF
open Interval128.Dy (Dy DI)
open RealFP.Roots (AllZero vec vec_getD vec_congr vec_length eq_vec forall2_vec inBoxes_vec
  set_vec qget delta kE tE nE ptBoxes fget unitBoxes kraw_alg Lay lay_mk kE_denote tE_denote
  nE_denote sum_delta allZero_iff ptBoxes_getD existsUnique_of subBoxes subBoxes_length
  inBoxes_sub)

noncomputable section

namespace RealFP.I128Q

set_option linter.concreteInstances false
variable [ExtTbl] [ExtSem]

/-! ### Mean value theorem across a box -/

theorem mvt_boxQ (F : IExpr) {bs : List (ℚ × ℚ)} {n : Nat} (hn : bs.length = n)
    (hd : Interval128.Dy.domOKQ (Interval128.Dy.boxes bs) F = true) {x y : Nat → ℝ}
    (hx : InBoxes (vec n x) bs) (hy : InBoxes (vec n y) bs) :
    ∃ a : Nat → ℝ, (∀ j < n, mem (a j) (Interval128.Dy.evalQ (Interval128.Dy.boxes bs) (F.deriv j))) ∧
      F.denote (vec n x) - F.denote (vec n y) = ∑ j ∈ Finset.range n, a j * (x j - y j) := by
  set X := Interval128.Dy.boxes bs
  let z : Nat → Nat → ℝ := fun r j => if j < r then x j else y j
  have hzb : ∀ r, InBoxes (vec n (z r)) bs := by
    intro r; rw [inBoxes_vec hn]; intro j hj
    have h1 := (inBoxes_vec hn).1 hx j hj; have h2 := (inBoxes_vec hn).1 hy j hj
    simp only [z]; split_ifs <;> assumption
  have hxm := RealFP.I128Q.boxes_mem hx
  have hym := RealFP.I128Q.boxes_mem hy
  have step : ∀ r < n, ∃ d, mem d (Interval128.Dy.evalQ X (F.deriv r)) ∧
      F.denote (vec n (z (r + 1))) - F.denote (vec n (z r)) = d * (x r - y r) := by
    intro r hr
    have hzm := RealFP.I128Q.boxes_mem (hzb r)
    have hxr : mem (x r) (X.getD r DI.zero) := by
      have := RealFP.I128Q.getD_mem hxm r; rwa [vec_getD x hr] at this
    have hyr : mem (y r) (X.getD r DI.zero) := by
      have := RealFP.I128Q.getD_mem hym r; rwa [vec_getD y hr] at this
    have hlen : r < (vec n (z r)).length := by simpa using hr
    obtain ⟨d, hdS, hmv⟩ := mvt_uIcc (S := fun d => mem d (Interval128.Dy.evalQ X (F.deriv r)))
      (φ := fun s => F.denote ((vec n (z r)).set r s)) (a := y r) (b := x r) (fun t ht => by
        have htX := seg_memQ hyr hxr ht
        exact ⟨_, evalQ_sound (forall2_setxQ hzm r htX) (F.deriv r),
          hasDerivAt_boxQ hzm hlen hd htX⟩)
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

/-! ### The check -/

/-- The enclosure lies in `[-q, q]`. -/
def inQQ (q : ℚ) (F : DI) : Bool := Interval128.Dy.gLe q F && Interval128.Dy.gGe (-q) F

/-- The enclosure lies in `[lo, hi]`. -/
def inLHQ (lo hi : ℚ) (F : DI) : Bool := Interval128.Dy.gGe lo F && Interval128.Dy.gLe hi F

/-- Krawczyk certificate at precision 128 (found by an untrusted search). -/
structure KCertQ where
  m : List ℚ
  Y : List (List ℚ)
  Z : List (List ℚ)
  q : ℚ
  deriving Repr, Inhabited

/-- Enclosures of `Fₖ(m)`. -/
def bEnvQ (n : Nat) (Fs : List IExpr) (mq : List ℚ) : List DI :=
  (List.range n).map fun k => Interval128.Dy.evalQ (Interval128.Dy.boxes (ptBoxes mq)) (fget Fs k)

/-- Interval Jacobian on the box, row-major. -/
def jEnvQ (n : Nat) (Fs : List IExpr) (bs : List (ℚ × ℚ)) : List DI :=
  (List.range (n * n)).map fun t =>
    Interval128.Dy.evalQ (Interval128.Dy.boxes bs) ((fget Fs (t / n)).deriv (t % n))

def rowOKQ (n : Nat) (bs : List (ℚ × ℚ)) (c : KCertQ) (env envT : List DI) (i : Nat) : Bool :=
  inLHQ (bs.getD i (0, 0)).1 (bs.getD i (0, 0)).2 (Interval128.Dy.evalQ env (kE n c.Y i)) &&
    inQQ c.q (Interval128.Dy.evalQ envT (tE n c.Y i)) &&
    inQQ c.q (Interval128.Dy.evalQ envT (nE n c.Y c.Z i))

/-- All rows, given the enclosures `B` of `F(m)` and `J` of the Jacobian (computed once). -/
def rowsOKQ (bs : List (ℚ × ℚ)) (c : KCertQ) (B J : List DI) : Bool :=
  (List.range bs.length).all (rowOKQ bs.length bs c
    (Interval128.Dy.boxes bs ++ Interval128.Dy.boxes (ptBoxes c.m) ++ B ++ J)
    (Interval128.Dy.boxes (unitBoxes bs.length) ++ Interval128.Dy.boxes (ptBoxes c.m) ++ B ++ J))

/-- **Krawczyk check** at precision 128 for `Fs = 0` on the box `bs`. -/
def krawCheckQ (Fs : List IExpr) (bs : List (ℚ × ℚ)) (c : KCertQ) : Bool :=
  Fs.length == bs.length && c.m.length == bs.length && decide (0 ≤ c.q) && decide (c.q < 1) &&
    (List.range bs.length).all (fun i =>
      decide ((bs.getD i (0, 0)).1 ≤ c.m.getD i 0 ∧ c.m.getD i 0 ≤ (bs.getD i (0, 0)).2)) &&
    Fs.all (Interval128.Dy.domOKQ (Interval128.Dy.boxes bs)) &&
    rowsOKQ bs c (bEnvQ bs.length Fs c.m) (jEnvQ bs.length Fs bs)

/-! ### Soundness -/

omit [ExtTbl] [ExtSem] in
theorem inQQ_sound {q : ℚ} {F : DI} (h : inQQ q F = true) {y : ℝ} (hy : mem y F) : |y| ≤ q := by
  simp only [inQQ, Bool.and_eq_true] at h
  have h1 := gLe_sound q F h.1 y hy
  have h2 := gGe_sound (-q) F h.2 y hy
  push_cast at h2
  exact abs_le.2 ⟨h2, h1⟩

omit [ExtTbl] [ExtSem] in
theorem inLHQ_sound {lo hi : ℚ} {F : DI} (h : inLHQ lo hi F = true) {y : ℝ} (hy : mem y F) :
    (lo : ℝ) ≤ y ∧ y ≤ hi := by
  simp only [inLHQ, Bool.and_eq_true] at h
  exact ⟨gGe_sound lo F h.1 y hy, gLe_sound hi F h.2 y hy⟩

section Sound

variable {Fs : List IExpr} {bs : List (ℚ × ℚ)} {c : KCertQ}

/-- Everything the check gives, unpacked. -/
structure FactsQ (Fs : List IExpr) (bs : List (ℚ × ℚ)) (c : KCertQ) : Prop where
  hF : Fs.length = bs.length
  hm : c.m.length = bs.length
  hq0 : 0 ≤ c.q
  hq1 : c.q < 1
  hmb : ∀ i < bs.length, (bs.getD i (0, 0)).1 ≤ c.m.getD i 0 ∧ c.m.getD i 0 ≤ (bs.getD i (0, 0)).2
  hdom : ∀ k, Interval128.Dy.domOKQ (Interval128.Dy.boxes bs) (fget Fs k) = true
  hrow : ∀ i < bs.length, rowOKQ bs.length bs c
      (Interval128.Dy.boxes bs ++ Interval128.Dy.boxes (ptBoxes c.m) ++ bEnvQ bs.length Fs c.m ++
        jEnvQ bs.length Fs bs)
      (Interval128.Dy.boxes (unitBoxes bs.length) ++ Interval128.Dy.boxes (ptBoxes c.m) ++
        bEnvQ bs.length Fs c.m ++ jEnvQ bs.length Fs bs) i = true

omit [ExtSem] in
theorem factsQ_of_check (h : krawCheckQ Fs bs c = true) : FactsQ Fs bs c := by
  simp only [krawCheckQ, rowsOKQ, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨hF, hm⟩, hq0⟩, hq1⟩, hmb⟩, hdom⟩, hrow⟩ := h
  refine ⟨hF, hm, hq0, hq1, hmb, fun k => ?_, hrow⟩
  unfold RealFP.Roots.fget
  by_cases hk : k < Fs.length
  · rw [List.getD_eq_getElem _ _ hk]; exact hdom _ (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ (by omega)]; rfl

def mRQ (c : KCertQ) (j : Nat) : ℝ := (c.m.getD j 0 : ℝ)
def FkQ (Fs : List IExpr) (n k : Nat) (x : Nat → ℝ) : ℝ := (fget Fs k).denote (vec n x)
def GvQ (Fs : List IExpr) (n : Nat) (Y : List (List ℚ)) (x : Nat → ℝ) (i : Nat) : ℝ :=
  x i - ∑ k ∈ Finset.range n, (qget Y i k : ℝ) * FkQ Fs n k x

omit [ExtSem] in
theorem inBoxes_mQ (hf : FactsQ Fs bs c) : InBoxes (vec bs.length (mRQ c)) (ptBoxes c.m) := by
  rw [inBoxes_vec (by simp [ptBoxes, hf.hm])]
  intro j _; rw [ptBoxes_getD]; exact ⟨le_rfl, le_rfl⟩

omit [ExtSem] in
theorem inBoxes_mQ' (hf : FactsQ Fs bs c) : InBoxes (vec bs.length (mRQ c)) bs := by
  rw [inBoxes_vec rfl]
  intro j hj; have := hf.hmb j hj
  exact ⟨by simp only [mRQ]; exact_mod_cast this.1, by simp only [mRQ]; exact_mod_cast this.2⟩

theorem env_memQ (hf : FactsQ Fs bs c) {l0 : List ℝ} {E0 : List DI}
    (h0 : List.Forall₂ mem l0 E0) {a : Nat → Nat → ℝ}
    (ha : ∀ k < bs.length, ∀ j < bs.length,
      mem (a k j) (Interval128.Dy.evalQ (Interval128.Dy.boxes bs) ((fget Fs k).deriv j))) :
    List.Forall₂ mem
      (l0 ++ vec bs.length (mRQ c) ++ vec bs.length (fun k => FkQ Fs bs.length k (mRQ c)) ++
        vec (bs.length * bs.length) (fun t => a (t / bs.length) (t % bs.length)))
      (E0 ++ Interval128.Dy.boxes (ptBoxes c.m) ++ bEnvQ bs.length Fs c.m ++
        jEnvQ bs.length Fs bs) := by
  have hM := RealFP.I128Q.boxes_mem (inBoxes_mQ hf)
  refine List.rel_append (List.rel_append (List.rel_append h0 hM) ?_) ?_
  · exact forall2_vec fun k _ => evalQ_sound hM (fget Fs k)
  · refine forall2_vec fun t ht => ?_
    have hn : 0 < bs.length := by
      rcases Nat.eq_zero_or_pos bs.length with h | h
      · simp [h] at ht
      · exact h
    exact ha _ (Nat.div_lt_of_lt_mul ht) _ (Nat.mod_lt _ hn)

theorem mvt_allQ (hf : FactsQ Fs bs c) {x y : Nat → ℝ} (hx : InBoxes (vec bs.length x) bs)
    (hy : InBoxes (vec bs.length y) bs) :
    ∃ a : Nat → Nat → ℝ, (∀ k < bs.length, ∀ j < bs.length,
      mem (a k j) (Interval128.Dy.evalQ (Interval128.Dy.boxes bs) ((fget Fs k).deriv j))) ∧
      ∀ k, FkQ Fs bs.length k x - FkQ Fs bs.length k y =
        ∑ j ∈ Finset.range bs.length, a k j * (x j - y j) := by
  have := fun k => mvt_boxQ (fget Fs k) rfl (hf.hdom k) hx hy
  choose a ha heq using this
  exact ⟨a, fun k _ j hj => ha k j hj, heq⟩

theorem maps_intoQ (hf : FactsQ Fs bs c) {x : Nat → ℝ} (hx : InBoxes (vec bs.length x) bs) :
    ∀ i < bs.length, ((bs.getD i (0, 0)).1 : ℝ) ≤ GvQ Fs bs.length c.Y x i ∧
      GvQ Fs bs.length c.Y x i ≤ ((bs.getD i (0, 0)).2 : ℝ) := by
  obtain ⟨a, ha, heq⟩ := mvt_allQ hf hx (inBoxes_mQ' hf)
  have hL := env_memQ hf (RealFP.I128Q.boxes_mem hx) ha
  have hlay := lay_mk bs.length x (mRQ c) (fun k => FkQ Fs bs.length k (mRQ c)) a
  intro i hi
  have hrow := hf.hrow i hi
  simp only [rowOKQ, Bool.and_eq_true] at hrow
  have hK := inLHQ_sound hrow.1.1 (evalQ_sound hL (kE bs.length c.Y i))
  rw [kE_denote hlay c.Y hi] at hK
  have e := kraw_alg hi (fun i k => (qget c.Y i k : ℝ)) x (mRQ c) (fun k => FkQ Fs bs.length k x)
    (fun k => FkQ Fs bs.length k (mRQ c)) a heq
  rw [GvQ, e]; exact hK

omit [ExtTbl] [ExtSem] in
theorem unit_inBoxes {n : Nat} {d : Nat → ℝ} (h : ∀ j < n, |d j| ≤ 1) :
    InBoxes (vec n d) (unitBoxes n) := by
  rw [inBoxes_vec (by simp [unitBoxes])]
  intro j hj
  have h1 : (unitBoxes n).getD j (0, 0) = (-1, 1) := by
    simp [unitBoxes, List.getD_eq_getElem?_getD, hj]
  rw [h1]; push_cast; exact abs_le.1 (h j hj)

theorem lipQ (hf : FactsQ Fs bs c) {x y : Nat → ℝ} (hx : InBoxes (vec bs.length x) bs)
    (hy : InBoxes (vec bs.length y) bs) {t : ℝ} (ht : 0 ≤ t)
    (hxy : ∀ j < bs.length, |x j - y j| ≤ t) :
    ∀ i < bs.length, |GvQ Fs bs.length c.Y x i - GvQ Fs bs.length c.Y y i| ≤ c.q * t := by
  intro i hi
  rcases ht.lt_or_eq with htp | ht0
  · obtain ⟨a, ha, heq⟩ := mvt_allQ hf hx hy
    let d : Nat → ℝ := fun j => (x j - y j) / t
    have hd : InBoxes (vec bs.length d) (unitBoxes bs.length) := unit_inBoxes fun j hj => by
      simp only [d]; rw [abs_div, abs_of_pos htp]; exact (div_le_one htp).2 (hxy j hj)
    have hL := env_memQ hf (RealFP.I128Q.boxes_mem hd) ha
    have hlay := lay_mk bs.length d (mRQ c) (fun k => FkQ Fs bs.length k (mRQ c)) a
    have hrow := hf.hrow i hi
    simp only [rowOKQ, Bool.and_eq_true] at hrow
    have hT := inQQ_sound hrow.1.2 (evalQ_sound hL (tE bs.length c.Y i))
    rw [tE_denote hlay c.Y i] at hT
    have e := kraw_alg hi (fun i k => (qget c.Y i k : ℝ)) x y (fun k => FkQ Fs bs.length k x)
      (fun k => FkQ Fs bs.length k y) a heq
    have e2 : GvQ Fs bs.length c.Y x i - GvQ Fs bs.length c.Y y i = t *
        ∑ j ∈ Finset.range bs.length, ((if i = j then 1 else 0) -
          ∑ k ∈ Finset.range bs.length, (qget c.Y i k : ℝ) * a k j) * d j := by
      rw [GvQ, GvQ, e, Finset.mul_sum]
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
    simp only [GvQ, FkQ, hv, hxi, sub_self, abs_zero, mul_zero, le_refl]

theorem y_injQ (hf : FactsQ Fs bs c) {u : Nat → ℝ}
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
  have hd : InBoxes (vec bs.length d) (unitBoxes bs.length) := unit_inBoxes fun j hj => by
    simp only [d]; rw [abs_div, abs_of_pos htp]
    exact (div_le_one htp).2 (hmax j (Finset.mem_range.2 hj))
  obtain ⟨a, ha, -⟩ := mvt_allQ hf (inBoxes_mQ' hf) (inBoxes_mQ' hf)
  have hL := env_memQ hf (RealFP.I128Q.boxes_mem hd) ha
  have hlay := lay_mk bs.length d (mRQ c) (fun k => FkQ Fs bs.length k (mRQ c)) a
  have hrow := hf.hrow jm hjm'
  simp only [rowOKQ, Bool.and_eq_true] at hrow
  have hN := inQQ_sound hrow.2 (evalQ_sound hL (nE bs.length c.Y c.Z jm))
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
  have : (c.q : ℝ) < 1 := by exact_mod_cast hf.hq1
  linarith

theorem zero_of_fixedQ (hf : FactsQ Fs bs c) {x : Nat → ℝ}
    (hfix : ∀ i < bs.length, GvQ Fs bs.length c.Y x i = x i) :
    ∀ k < bs.length, FkQ Fs bs.length k x = 0 :=
  y_injQ hf (u := fun k => FkQ Fs bs.length k x) fun i hi => by
    have := hfix i hi; simp only [GvQ] at this; linarith

/-- **Existence** (Banach fixed point theorem on the box). -/
theorem kraw_existsQ (h : krawCheckQ Fs bs c = true) : ∃ xs, InBoxes xs bs ∧ AllZero Fs xs := by
  have hf := factsQ_of_check h
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
  have hm0 : (fun i : Fin n => mRQ c i) ∈ S := by
    rw [hmem]
    have : vec n (toN fun i : Fin n => mRQ c i) = vec n (mRQ c) :=
      vec_congr fun j hj => by simp [toN, hj]
    rw [this]; exact inBoxes_mQ' hf
  have : Nonempty S := ⟨⟨_, hm0⟩⟩
  let Gf : (Fin n → ℝ) → Fin n → ℝ := fun v i => GvQ Fs n c.Y (toN v) i
  have hmaps : ∀ v ∈ S, Gf v ∈ S := fun v hv i => maps_intoQ hf ((hmem v).1 hv) i i.2
  let f : S → S := fun v => ⟨Gf v.1, hmaps v.1 v.2⟩
  have hq0 : (0 : ℝ) ≤ c.q := by exact_mod_cast hf.hq0
  have hK : ContractingWith (Real.toNNReal c.q) f := by
    refine ⟨by rw [Real.toNNReal_lt_one]; exact_mod_cast hf.hq1,
      LipschitzWith.of_dist_le_mul fun v w => ?_⟩
    rw [Real.coe_toNNReal _ hq0, Subtype.dist_eq, Subtype.dist_eq]
    refine (dist_pi_le_iff (mul_nonneg hq0 dist_nonneg)).2 fun i => ?_
    rw [Real.dist_eq]
    refine lipQ hf ((hmem _).1 v.2) ((hmem _).1 w.2) dist_nonneg (fun j hj => ?_) i i.2
    rw [show toN v.1 j = v.1 ⟨j, hj⟩ from dif_pos hj, show toN w.1 j = w.1 ⟨j, hj⟩ from dif_pos hj]
    rw [← Real.dist_eq]; exact dist_le_pi_dist v.1 w.1 ⟨j, hj⟩
  have hp := ContractingWith.fixedPoint_isFixedPt (f := f) hK
  set p := ContractingWith.fixedPoint f hK
  have hfix : ∀ i < n, GvQ Fs n c.Y (toN p.1) i = toN p.1 i := by
    intro i hi
    have := congrFun (congrArg Subtype.val hp) ⟨i, hi⟩
    simp only [toN, hi, ↓reduceDIte]; exact this
  have hz := zero_of_fixedQ hf hfix
  refine ⟨vec n (toN p.1), (hmem _).1 p.2, (allZero_iff hf.hF).2 fun k hk => hz k hk⟩

/-- **Uniqueness**: two zeros in the box coincide (`G` is a contraction). -/
theorem kraw_uniqueQ (h : krawCheckQ Fs bs c = true) {xs ys : List ℝ} (hx : InBoxes xs bs)
    (hzx : AllZero Fs xs) (hy : InBoxes ys bs) (hzy : AllZero Fs ys) : xs = ys := by
  have hf := factsQ_of_check h
  have lx : xs.length = bs.length := List.Forall₂.length_eq hx
  have ly : ys.length = bs.length := List.Forall₂.length_eq hy
  let x : Nat → ℝ := fun j => xs.getD j 0
  let y : Nat → ℝ := fun j => ys.getD j 0
  have ex : xs = vec bs.length x := by conv_lhs => rw [eq_vec xs]
                                       rw [lx]
  have ey : ys = vec bs.length y := by conv_lhs => rw [eq_vec ys]
                                       rw [ly]
  rw [ex] at hx hzx ⊢; rw [ey] at hy hzy ⊢
  have fx : ∀ i < bs.length, GvQ Fs bs.length c.Y x i = x i := fun i _ => by
    have hz : ∀ k ∈ Finset.range bs.length, (qget c.Y i k : ℝ) * FkQ Fs bs.length k x = 0 :=
      fun k hk => by rw [FkQ, (allZero_iff hf.hF).1 hzx k (Finset.mem_range.1 hk), mul_zero]
    simp only [GvQ, Finset.sum_eq_zero hz, sub_zero]
  have fy : ∀ i < bs.length, GvQ Fs bs.length c.Y y i = y i := fun i _ => by
    have hz : ∀ k ∈ Finset.range bs.length, (qget c.Y i k : ℝ) * FkQ Fs bs.length k y = 0 :=
      fun k hk => by rw [FkQ, (allZero_iff hf.hF).1 hzy k (Finset.mem_range.1 hk), mul_zero]
    simp only [GvQ, Finset.sum_eq_zero hz, sub_zero]
  apply vec_congr
  intro j hj
  obtain ⟨jm, hjm, hmax⟩ := Finset.exists_max_image (Finset.range bs.length) (fun j => |x j - y j|)
    ⟨j, Finset.mem_range.2 hj⟩
  have hjm' := Finset.mem_range.1 hjm
  have hl := lipQ hf hx hy (abs_nonneg (x jm - y jm))
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

/-- **Krawczyk at 128, existence and uniqueness** for points of any type with a coordinate list. -/
theorem kraw_existsUniqueQ {T : Type} (Fs : List IExpr) (bs : List (ℚ × ℚ)) (c : KCertQ)
    (toL : T → List ℝ) (ofL : List ℝ → T) (hto : ∀ xs, xs.length = bs.length → toL (ofL xs) = xs)
    (hinj : ∀ p q, toL p = toL q → p = q) (h : krawCheckQ Fs bs c = true) :
    ∃! p : T, InBoxes (toL p) bs ∧ AllZero Fs (toL p) :=
  existsUnique_of toL ofL (fun xs => InBoxes xs bs ∧ AllZero Fs xs) bs.length
    (fun _ h => List.Forall₂.length_eq h.1) hto hinj (kraw_existsQ h)
    (fun _ _ h1 h2 => kraw_uniqueQ h h1.1 h1.2 h2.1 h2.2)

/-- **Krawczyk at 128, existence in a sub-box** `bs' ⊆ bs`. -/
theorem kraw_exists_inQ {T : Type} (Fs : List IExpr) (bs bs' : List (ℚ × ℚ)) (c : KCertQ)
    (toL : T → List ℝ) (ofL : List ℝ → T) (hto : ∀ xs, xs.length = bs.length → toL (ofL xs) = xs)
    (h : (subBoxes bs' bs && krawCheckQ Fs bs' c) = true) :
    ∃ p : T, InBoxes (toL p) bs ∧ AllZero Fs (toL p) := by
  simp only [Bool.and_eq_true] at h
  obtain ⟨xs, h1, h2⟩ := kraw_existsQ h.2
  have e := hto xs ((List.Forall₂.length_eq h1).trans (subBoxes_length h.1))
  exact ⟨ofL xs, by rw [e]; exact ⟨inBoxes_sub h1 h.1, h2⟩⟩

end RealFP.I128Q
