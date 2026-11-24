/-
Soundness of the Interval128 reflective checker (`Interval128.Refl.checkD`) over `ℝ`: the
`(precision := 128)` path of the `interval` / `realfp` tactics.

* `evalD_sound` — `e.denote xs ∈ toSet (evalD env e)` whenever each `xs[i] ∈ toSet env[i]`.
* `checkD_sound` — an accepted bisection certificate proves the goal predicate on the box.
* `prove_le` / `prove_lt` / `prove_ge` / `prove_gt` — the statements the tactic uses.

Functions without a double-double implementation go through the Interval64 evaluator
(`lift1` / `lift2`); their soundness is `RealFP.eval_sound` and `evalK_toI`.
-/
import RealFPMathlib.I128Mem
import RealFPMathlib.IntervalSound
import Mathlib.Analysis.Real.Pi.Bounds

open Interval64 Interval64.KF
open Interval128.Refl (I zeroD oneD hull64 lift1 lift2 divD invD sqrtD absD mulPow powD piLo piHi
  piD evalD leftAt rightAt)
open Interval64.Spec Interval64Proofs.FloatBits

noncomputable section

namespace RealFP.I128

/-! ### Endpoint monotonicity -/

theorem loIn_mono {h l : Float} {x y : ℝ} (hx : loIn h l x) (hxy : x ≤ y) : loIn h l y := by
  rcases hx with ⟨a, b, ha, hb, i⟩ | ⟨hl0, hn, hle⟩
  · exact Or.inl ⟨a, b, ha, hb, le_trans i hxy⟩
  · exact Or.inr ⟨hl0, hn, le_trans hle (EReal.coe_le_coe_iff.2 hxy)⟩

theorem hiIn_mono {h l : Float} {x y : ℝ} (hy : hiIn h l y) (hxy : x ≤ y) : hiIn h l x := by
  rcases hy with ⟨a, b, ha, hb, i⟩ | ⟨hl0, hn, hle⟩
  · exact Or.inl ⟨a, b, ha, hb, le_trans hxy i⟩
  · exact Or.inr ⟨hl0, hn, le_trans (EReal.coe_le_coe_iff.2 hxy) hle⟩

theorem fv_of_bits {f : Float} {q : ℚ} (h : bitsToRat? f.toBits = some q) : Fv f (q : ℝ) :=
  toReal?_of_bitsToRat? h

theorem ddRat_vals {h l : Float} {u : ℚ} (hu : Interval128.Interval128.ddRat? h l = some u) :
    ∃ a b : ℚ, Fv h (a : ℝ) ∧ Fv l (b : ℝ) ∧ u = a + b := by
  unfold Interval128.Interval128.ddRat? at hu
  split at hu
  · rename_i a b ha hb
    simp only [Option.some.injEq] at hu
    exact ⟨a, b, fv_of_bits ha, fv_of_bits hb, hu.symm⟩
  · simp at hu

/-! ### Fallback through Interval64 -/

theorem hull64_mem {X : I} {x : ℝ} {K : KI} (h : hull64 X = some K) (hx : x ∈ toSet X) :
    x ∈ (toI K).toSet ∧ WF K := by
  unfold hull64 at h
  dsimp only at h
  split_ifs at h with hn
  simp only [Option.some.injEq] at h
  subst h
  simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hn
  refine ⟨?_, ofI_wf _⟩
  have hset : (toI (ofI (Interval128.Interval128.toInterval64 X))).toSet =
      (Interval128.Interval128.toInterval64 X).toSet := by
    simp only [Interval64.toSet, toI, ofI, toBits_toF_toBits hn.1, toBits_toF_toBits hn.2]
  rw [hset]; exact mem_toInterval64 hx

set_option linter.concreteInstances false
variable [ExtTbl] [ExtSem]

theorem lift1_mem (f : IExpr) {X : I} {x : ℝ} (hx : x ∈ toSet X) :
    f.denote [x] ∈ toSet (lift1 f X) := by
  unfold lift1
  split
  · rename_i K hK
    obtain ⟨hm, hw⟩ := hull64_mem hK hx
    apply mem_ofInterval64
    have hwf : ∀ Y ∈ [K], WF Y := by simpa using hw
    rw [toIv_eq, (evalK_toI hwf f).1]
    exact eval_sound (List.Forall₂.cons (by simpa using hm) List.Forall₂.nil) f
  · exact mem_whole _

theorem lift2_mem (f : IExpr) {X Y : I} {x y : ℝ} (hx : x ∈ toSet X) (hy : y ∈ toSet Y) :
    f.denote [x, y] ∈ toSet (lift2 f X Y) := by
  unfold lift2
  split
  · rename_i K L hK hL
    obtain ⟨hm, hw⟩ := hull64_mem hK hx
    obtain ⟨hm', hw'⟩ := hull64_mem hL hy
    apply mem_ofInterval64
    have hwf : ∀ Z ∈ [K, L], WF Z := by simp [hw, hw']
    rw [toIv_eq, (evalK_toI hwf f).1]
    exact eval_sound (List.Forall₂.cons (by simpa using hm)
      (List.Forall₂.cons (by simpa using hm') List.Forall₂.nil)) f
  · exact mem_whole _

omit [ExtTbl] [ExtSem] in
theorem mem_oneD : (1 : ℝ) ∈ toSet oneD := by
  have := mem_ofRat 1; rw [Rat.cast_one] at this; exact this

omit [ExtTbl] [ExtSem] in
theorem divD_mem {X Y : I} {x y : ℝ} (hx : x ∈ toSet X) (hy : y ∈ toSet Y) :
    x / y ∈ toSet (divD X Y) := by
  unfold divD
  split_ifs with c
  · simp only [Bool.and_eq_true, Bool.or_eq_true] at c
    obtain ⟨b1, b2, b3, b4, fb1, fb2, fb3, fb4⟩ := isFin_vals c.1
    have hy0 : y ≠ 0 := by
      rcases c.2 with c2 | c2
      · have := (pos_iff fb1 fb2).1 c2
        have := loIn_val hy.1 fb1 fb2
        exact ne_of_gt (by linarith)
      · have := (neg_iff fb3 fb4).1 c2
        have := hiIn_val hy.2 fb3 fb4
        exact ne_of_lt (by linarith)
    exact mem_div hx hy hy0
  · exact mem_whole _

omit [ExtTbl] [ExtSem] in
theorem invD_mem {X : I} {x : ℝ} (hx : x ∈ toSet X) : x⁻¹ ∈ toSet (invD X) := by
  rw [inv_eq_one_div]; exact divD_mem mem_oneD hx

theorem sqrtD_mem {X : I} {x : ℝ} (hx : x ∈ toSet X) : Real.sqrt x ∈ toSet (sqrtD X) := by
  unfold sqrtD
  split_ifs with c
  · simp only [Bool.and_eq_true] at c
    obtain ⟨a1, a2, a3, a4, fa1, fa2, fa3, fa4⟩ := isFin_vals c.1
    have := (nonneg_iff fa1 fa2).1 c.2
    have := loIn_val hx.1 fa1 fa2
    exact mem_sqrt hx (by linarith)
  · exact lift1_mem (.sqrt (.var 0)) hx

theorem absD_mem {X : I} {x : ℝ} (hx : x ∈ toSet X) : |x| ∈ toSet (absD X) := by
  unfold absD
  split_ifs with c c'
  · simp only [Bool.and_eq_true] at c
    obtain ⟨a1, a2, a3, a4, fa1, fa2, fa3, fa4⟩ := isFin_vals c.1
    have := (nonneg_iff fa1 fa2).1 c.2
    have := loIn_val hx.1 fa1 fa2
    rw [abs_of_nonneg (by linarith)]; exact hx
  · simp only [Bool.and_eq_true] at c'
    obtain ⟨a1, a2, a3, a4, fa1, fa2, fa3, fa4⟩ := isFin_vals c'.1
    have := (nonpos_iff fa3 fa4).1 c'.2
    have := hiIn_val hx.2 fa3 fa4
    rw [abs_of_nonpos (by linarith)]; exact mem_neg hx
  · exact lift1_mem (.abs (.var 0)) hx

omit [ExtTbl] [ExtSem] in
theorem mulPow_mem {X : I} {x : ℝ} (hx : x ∈ toSet X) (n : Nat) : x ^ n ∈ toSet (mulPow X n) := by
  induction n with
  | zero => rw [pow_zero]; exact mem_oneD
  | succ n ih => rw [pow_succ]; exact mem_mul ih hx

theorem powD_mem {X : I} {x : ℝ} (hx : x ∈ toSet X) (n : Nat) : x ^ n ∈ toSet (powD X n) := by
  unfold powD
  split_ifs with c
  · have he : Even n := Nat.even_iff.2 (by simpa using c)
    rw [← he.pow_abs]; exact mulPow_mem (absD_mem hx) n
  · exact mulPow_mem hx n

omit [ExtTbl] [ExtSem] in
theorem piD_mem : Real.pi ∈ toSet piD := by
  have h1 : ((piLo : ℚ) : ℝ) ≤ Real.pi := by
    have := Real.pi_gt_d20; simp only [piLo]; push_cast; linarith
  have h2 : Real.pi ≤ ((piHi : ℚ) : ℝ) := by
    have := Real.pi_lt_d20; simp only [piHi]; push_cast; linarith
  exact ⟨loIn_mono (ddOfRatDown_lo piLo) h1, hiIn_mono (ddOfRatUp_hi piHi) h2⟩

omit [ExtTbl] [ExtSem] in
theorem zero_mem_zeroD : (0 : ℝ) ∈ toSet zeroD := mem_point fv_zero

omit [ExtTbl] [ExtSem] in
theorem getD_memD {xs : List ℝ} {env : List I}
    (h : List.Forall₂ (fun x X => x ∈ toSet X) xs env) (i : Nat) :
    xs.getD i 0 ∈ toSet (env.getD i zeroD) := by
  induction h generalizing i with
  | nil => simpa using zero_mem_zeroD
  | cons hxX _ ih =>
    cases i with
    | zero => simpa using hxX
    | succ n => simpa using ih n

theorem evalD_sound {xs : List ℝ} {env : List I}
    (h : List.Forall₂ (fun x X => x ∈ toSet X) xs env) :
    ∀ e : IExpr, e.denote xs ∈ toSet (evalD env e) := by
  intro e
  induction e with
  | var i => exact getD_memD h i
  | rat q => exact mem_ofRat q
  | add a b iha ihb => exact mem_add iha ihb
  | sub a b iha ihb => exact mem_sub iha ihb
  | mul a b iha ihb => exact mem_mul iha ihb
  | div a b iha ihb => exact divD_mem iha ihb
  | neg a iha => exact mem_neg iha
  | inv a iha => exact invD_mem iha
  | sqrt a iha => exact sqrtD_mem iha
  | abs a iha => exact absD_mem iha
  | pow a n iha => exact powD_mem iha n
  | exp a iha => exact lift1_mem (.exp (.var 0)) iha
  | log a iha => exact lift1_mem (.log (.var 0)) iha
  | sin a iha => exact lift1_mem (.sin (.var 0)) iha
  | cos a iha => exact lift1_mem (.cos (.var 0)) iha
  | pi => exact piD_mem
  | atan a iha => exact lift1_mem (.atan (.var 0)) iha
  | atan2 a b iha ihb => exact lift2_mem (.atan2 (.var 0) (.var 1)) iha ihb
  | sinh a iha => exact lift1_mem (.sinh (.var 0)) iha
  | cosh a iha => exact lift1_mem (.cosh (.var 0)) iha
  | tanh a iha => exact lift1_mem (.tanh (.var 0)) iha
  | log2 a iha => exact lift1_mem (.log2 (.var 0)) iha
  | log10 a iha => exact lift1_mem (.log10 (.var 0)) iha
  | tan a iha => exact lift1_mem (.tan (.var 0)) iha
  | asin a iha => exact lift1_mem (.asin (.var 0)) iha
  | acos a iha => exact lift1_mem (.acos (.var 0)) iha
  | ext k d a _ iha => exact lift1_mem (.ext k d (.var 0)) iha

/-! ### Bisection -/

omit [ExtTbl] [ExtSem] in
theorem split_memD {X : I} {y : ℝ} (q : ℚ) (hy : y ∈ toSet X) :
    y ∈ toSet (leftAt X q) ∨ y ∈ toSet (rightAt X q) := by
  rcases le_total y (q : ℝ) with h | h
  · exact Or.inl ⟨hy.1, hiIn_mono (ddOfRatUp_hi q) h⟩
  · exact Or.inr ⟨loIn_mono (ddOfRatDown_lo q) h, hy.2⟩


omit [ExtTbl] [ExtSem] in
theorem forall2_setD {xs : List ℝ} {env : List I}
    (h : List.Forall₂ (fun x X => x ∈ toSet X) xs env) (i : Nat) {Y : I}
    (hY : xs.getD i 0 ∈ toSet Y) :
    List.Forall₂ (fun x X => x ∈ toSet X) xs (env.set i Y) := by
  induction h generalizing i with
  | nil => simp
  | cons hxX _ ih =>
    cases i with
    | zero => exact List.Forall₂.cons (by simpa using hY) (by assumption)
    | succ n => exact List.Forall₂.cons hxX (ih n (by simpa using hY))

theorem checkD_sound (e : IExpr) (g : I → Bool) (P : ℝ → Prop)
    (hg : ∀ F, g F = true → ∀ y ∈ toSet F, P y) :
    ∀ (c : Interval128.Refl.Cert) (env : List I) (xs : List ℝ),
      List.Forall₂ (fun x X => x ∈ toSet X) xs env →
      Interval128.Refl.checkD e g c env = true → P (e.denote xs) := by
  intro c
  induction c with
  | leaf =>
    intro env xs hxs hc
    exact hg _ hc _ (evalD_sound hxs e)
  | split i q l r ihl ihr =>
    intro env xs hxs hc
    simp only [Interval128.Refl.checkD, Bool.and_eq_true] at hc
    have hx := getD_memD hxs i
    rcases split_memD q hx with h1 | h1
    · exact ihl _ xs (forall2_setD hxs i h1) hc.1
    · exact ihr _ xs (forall2_setD hxs i h1) hc.2

/-! ### Goal predicates -/

omit [ExtTbl] [ExtSem] in
theorem gLe_sound (c : ℚ) : ∀ F, Interval128.Refl.gLe c F = true → ∀ y ∈ toSet F, y ≤ (c : ℝ) := by
  intro F hg y hy
  unfold Interval128.Refl.gLe at hg
  split at hg
  · rename_i u hu
    obtain ⟨a, b, ha, hb, rfl⟩ := ddRat_vals hu
    have := hiIn_val hy.2 ha hb
    have h2 : ((a + b : ℚ) : ℝ) ≤ c := by exact_mod_cast of_decide_eq_true hg
    push_cast at h2; linarith
  · simp at hg

omit [ExtTbl] [ExtSem] in
theorem gLt_sound (c : ℚ) : ∀ F, Interval128.Refl.gLt c F = true → ∀ y ∈ toSet F, y < (c : ℝ) := by
  intro F hg y hy
  unfold Interval128.Refl.gLt at hg
  split at hg
  · rename_i u hu
    obtain ⟨a, b, ha, hb, rfl⟩ := ddRat_vals hu
    have := hiIn_val hy.2 ha hb
    have h2 : ((a + b : ℚ) : ℝ) < c := by exact_mod_cast of_decide_eq_true hg
    push_cast at h2; linarith
  · simp at hg

omit [ExtTbl] [ExtSem] in
theorem gGe_sound (c : ℚ) : ∀ F, Interval128.Refl.gGe c F = true → ∀ y ∈ toSet F, (c : ℝ) ≤ y := by
  intro F hg y hy
  unfold Interval128.Refl.gGe at hg
  split at hg
  · rename_i u hu
    obtain ⟨a, b, ha, hb, rfl⟩ := ddRat_vals hu
    have := loIn_val hy.1 ha hb
    have h2 : (c : ℝ) ≤ ((a + b : ℚ) : ℝ) := by exact_mod_cast of_decide_eq_true hg
    push_cast at h2; linarith
  · simp at hg

omit [ExtTbl] [ExtSem] in
theorem gGt_sound (c : ℚ) : ∀ F, Interval128.Refl.gGt c F = true → ∀ y ∈ toSet F, (c : ℝ) < y := by
  intro F hg y hy
  unfold Interval128.Refl.gGt at hg
  split at hg
  · rename_i u hu
    obtain ⟨a, b, ha, hb, rfl⟩ := ddRat_vals hu
    have := loIn_val hy.1 ha hb
    have h2 : (c : ℝ) < ((a + b : ℚ) : ℝ) := by exact_mod_cast of_decide_eq_true hg
    push_cast at h2; linarith
  · simp at hg

/-! ### Entry points for the tactic -/

omit [ExtTbl] [ExtSem] in
theorem boxes_memD {xs : List ℝ} {bs : List (ℚ × ℚ)} (h : InBoxes xs bs) :
    List.Forall₂ (fun x X => x ∈ toSet X) xs (Interval128.Refl.boxes bs) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hx _ ih =>
    exact List.Forall₂.cons ⟨loIn_mono (ddOfRatDown_lo _) hx.1, hiIn_mono (ddOfRatUp_hi _) hx.2⟩ ih

theorem prove_le (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : Interval128.Refl.Cert)
    (h : Interval128.Refl.checkD e (Interval128.Refl.gLe c) cert (Interval128.Refl.boxes bs) = true) (xs : List ℝ)
    (hxs : InBoxes xs bs) : e.denote xs ≤ (c : ℝ) :=
  checkD_sound e _ _ (gLe_sound c) cert _ xs (boxes_memD hxs) h

theorem prove_lt (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : Interval128.Refl.Cert)
    (h : Interval128.Refl.checkD e (Interval128.Refl.gLt c) cert (Interval128.Refl.boxes bs) = true) (xs : List ℝ)
    (hxs : InBoxes xs bs) : e.denote xs < (c : ℝ) :=
  checkD_sound e _ _ (gLt_sound c) cert _ xs (boxes_memD hxs) h

theorem prove_ge (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : Interval128.Refl.Cert)
    (h : Interval128.Refl.checkD e (Interval128.Refl.gGe c) cert (Interval128.Refl.boxes bs) = true) (xs : List ℝ)
    (hxs : InBoxes xs bs) : (c : ℝ) ≤ e.denote xs :=
  checkD_sound e _ _ (gGe_sound c) cert _ xs (boxes_memD hxs) h

theorem prove_gt (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : Interval128.Refl.Cert)
    (h : Interval128.Refl.checkD e (Interval128.Refl.gGt c) cert (Interval128.Refl.boxes bs) = true) (xs : List ℝ)
    (hxs : InBoxes xs bs) : (c : ℝ) < e.denote xs :=
  checkD_sound e _ _ (gGt_sound c) cert _ xs (boxes_memD hxs) h

end RealFP.I128
