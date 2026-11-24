/-
Soundness of the 128-bit elementary functions of `Interval128/Dyadic.lean` (`exp`, `log`,
`sin`, `cos`, `sinh`, `cosh`, `tanh`, `logb 2`, `logb 10`) over `ℝ`.

* Taylor polynomials: `mem_horner`, `polyR_coefs`; remainders `Real.exp_bound`,
  `Complex.exp_bound` (at `y * I`), `Real.abs_log_sub_add_sum_range_le`.
* Argument reduction: `exp (y 2^s) = exp y ^ (2^s)` (`mem_sqIter`), double angles
  (`mem_dblIter`), `log x = 2^j log (√…√x)` (`log_sqrt_iter`).
-/
import RealFPMathlib.I128DyBase

open Interval64 Interval64.KF
open Interval128.Dy (Dy DI)
open Finset

noncomputable section

namespace RealFP.I128Q

/-! ### Small interval facts -/

theorem mem_pt (d : Dy) : mem (val d) (DI.pt d) :=
  ⟨by rintro l ⟨⟩; exact le_rfl, by rintro u ⟨⟩; exact le_rfl⟩

theorem mem_pm {r : ℚ} {x : ℝ} (h : |x| ≤ (r : ℝ)) : mem x (DI.pm r) := by
  have := abs_le.1 h
  refine ⟨by rintro l ⟨⟩; exact le_trans (val_ofRatDn _) (by push_cast; linarith),
    by rintro u ⟨⟩; exact le_trans this.2 (val_ofRatUp _)⟩

theorem val_scale (j : ℤ) (d : Dy) : val (Interval128.Dy.Dy.scale j d) = val d * (2 : ℝ) ^ j := by
  simp only [val, Interval128.Dy.Dy.scale]; rw [zpow_add₀ (by norm_num)]; ring

theorem mem_scale (j : ℤ) {X : DI} {x : ℝ} (hx : mem x X) : mem (x * (2 : ℝ) ^ j) (DI.scale j X) := by
  have hp := two_zpow_pos j
  constructor
  · intro l hl
    simp only [DI.scale, Option.map_eq_some_iff] at hl
    obtain ⟨a, ha, rfl⟩ := hl
    rw [val_scale]; exact mul_le_mul_of_nonneg_right (hx.1 a ha) hp.le
  · intro u hu
    simp only [DI.scale, Option.map_eq_some_iff] at hu
    obtain ⟨a, ha, rfl⟩ := hu
    rw [val_scale]; exact mul_le_mul_of_nonneg_right (hx.2 a ha) hp.le

theorem mem_zeroD : mem 0 DI.zero :=
  ⟨by rintro l ⟨⟩; rw [val_zero], by rintro l ⟨⟩; rw [val_zero]⟩

theorem mem_ofRat' (q : ℚ) {x : ℝ} (h : x = q) : mem x (DI.ofRat q) := h ▸ mem_ofRat q

/-- Scaled point: `val ⟨m, e - s⟩ * 2^s = val d`. -/
theorem val_halve (d : Dy) (s : ℕ) : val ⟨d.m, d.e - s⟩ * (2 : ℝ) ^ s = val d := by
  simp only [val]; rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num)]; congr 2; ring

theorem small_abs {y : Dy} (h : Interval128.Dy.small y = true) : |val y| ≤ 1 / 256 := by
  unfold Interval128.Dy.small at h
  have h' := of_decide_eq_true h
  rw [← toRat_val]
  have h1 := (Rat.cast_le (K := ℝ)).2 h'.1
  have h2 := (Rat.cast_le (K := ℝ)).2 h'.2
  push_cast at h1 h2
  exact abs_le.2 ⟨h1, h2⟩

/-! ### Polynomials -/

/-- `c₀ + x (c₁ + x (…))`. -/
def polyR : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => c + x * polyR cs x

theorem mem_mulPt (d : Dy) {X : DI} {x : ℝ} (hx : mem x X) :
    mem (val d * x) (DI.mulPt d X) := by
  unfold DI.mulPt
  split
  · rename_i l h hl hh
    have h1 := hx.1 l hl; have h2 := hx.2 h hh
    split
    · rename_i hd
      have hd' : (0 : ℝ) ≤ val d := by
        simp only [val]; exact mul_nonneg (by exact_mod_cast hd) (zpow_nonneg (by norm_num) _)
      constructor
      · rintro a ⟨⟩
        refine le_trans (val_rdn' _) ?_
        rw [val_mulX]; exact mul_le_mul_of_nonneg_left h1 hd'
      · rintro a ⟨⟩
        refine le_trans ?_ (val_rup' _)
        rw [val_mulX]; exact mul_le_mul_of_nonneg_left h2 hd'
    · rename_i hd
      have hd' : val d ≤ 0 := by
        simp only [val]
        exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (le_of_lt (not_le.1 hd)))
          (zpow_nonneg (by norm_num) _)
      constructor
      · rintro a ⟨⟩
        refine le_trans (val_rdn' _) ?_
        rw [val_mulX]; exact mul_le_mul_of_nonpos_left h2 hd'
      · rintro a ⟨⟩
        refine le_trans ?_ (val_rup' _)
        rw [val_mulX]; exact mul_le_mul_of_nonpos_left h1 hd'
  · exact mem_whole _

theorem mem_horner (cs : List ℚ) (d : Dy) :
    mem (polyR cs (val d)) (Interval128.Dy.horner cs d) := by
  induction cs with
  | nil => exact mem_zeroD
  | cons c cs ih =>
    unfold Interval128.Dy.horner; exact mem_add (mem_ofRat c) (mem_mulPt d ih)

theorem polyR_coefs (f : ℕ → ℚ) (x : ℝ) :
    ∀ n k, polyR (Interval128.Dy.coefs f k n) x = ∑ m ∈ range n, (f (k + m) : ℝ) * x ^ m := by
  intro n
  induction n with
  | zero => intro k; simp [Interval128.Dy.coefs, polyR]
  | succ n ih =>
    intro k
    simp only [Interval128.Dy.coefs, polyR, ih (k + 1)]
    rw [sum_range_succ', mul_sum]
    simp only [pow_zero, mul_one, add_zero, pow_succ]
    rw [add_comm]; congr 1
    apply sum_congr rfl; intro m _
    rw [show k + (m + 1) = k + 1 + m by ring]; ring

theorem fact_eq (n : ℕ) : Interval128.Dy.fact n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Interval128.Dy.fact, ih, Nat.factorial_succ]

theorem remT_bound {y : ℝ} (hy : |y| ≤ 1 / 256) :
    |y| ^ Interval128.Dy.nT * ((Interval128.Dy.nT.succ : ℝ) /
      (Interval128.Dy.nT.factorial * Interval128.Dy.nT)) ≤ ((Interval128.Dy.remT : ℚ) : ℝ) := by
  have hc : (0 : ℝ) ≤ (Interval128.Dy.nT.succ : ℝ) / (Interval128.Dy.nT.factorial * Interval128.Dy.nT) := by
    positivity
  have hp : |y| ^ Interval128.Dy.nT ≤ (1 / 256 : ℝ) ^ Interval128.Dy.nT :=
    pow_le_pow_left₀ (abs_nonneg _) hy _
  refine le_trans (mul_le_mul_of_nonneg_right hp hc) (le_of_eq ?_)
  simp only [Interval128.Dy.remT, fact_eq]
  push_cast; ring

/-! ### `exp` -/

theorem mem_taylor (cs : List ℚ) (y : Dy) {f : ℝ} {r : ℚ} (h : |f - polyR cs (val y)| ≤ (r : ℝ)) :
    mem f (DI.add (Interval128.Dy.horner cs y) (DI.pm r)) := by
  have := mem_add (mem_horner cs y) (mem_pm h)
  rwa [add_sub_cancel] at this

theorem expCoef_sum (y : ℝ) (n : ℕ) :
    polyR (Interval128.Dy.coefs Interval128.Dy.expCoef 0 n) y = ∑ m ∈ range n, y ^ m / m.factorial := by
  rw [polyR_coefs]
  apply sum_congr rfl; intro m _
  simp only [Interval128.Dy.expCoef, zero_add, fact_eq]; push_cast; ring

theorem nT_pos : 0 < Interval128.Dy.nT := by decide

theorem exp_taylor (y : Dy) (hy : |val y| ≤ 1 / 256) :
    mem (Real.exp (val y)) (DI.add (Interval128.Dy.horner (Interval128.Dy.coefs
      Interval128.Dy.expCoef 0 Interval128.Dy.nT) y) (DI.pm Interval128.Dy.remT)) := by
  apply mem_taylor
  rw [expCoef_sum]
  exact le_trans (Real.exp_bound (by linarith) nT_pos) (remT_bound hy)

theorem mem_sqIter : ∀ (s : ℕ) {X : DI} {t : ℝ}, mem (Real.exp t) X →
    mem (Real.exp (t * (2 : ℝ) ^ s)) (Interval128.Dy.sqIter s X) := by
  intro s
  induction s with
  | zero => intro X t h; simpa [Interval128.Dy.sqIter] using h
  | succ n ih =>
    intro X t h
    simp only [Interval128.Dy.sqIter]
    have h2 : mem (Real.exp (t * 2)) (DI.mul X X) := by
      rw [show t * 2 = t + t by ring, Real.exp_add]; exact mem_mul h h
    have := ih h2
    rwa [mul_assoc, ← pow_succ'] at this

theorem mem_expPt (d : Dy) : mem (Real.exp (val d)) (Interval128.Dy.expPt d) := by
  unfold Interval128.Dy.expPt
  dsimp only
  split_ifs with h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have := mem_sqIter (Interval128.Dy.halvings d) (exp_taylor _ (small_abs h.1))
    rwa [val_halve] at this
  · exact mem_whole _

theorem mem_exp {X : DI} {x : ℝ} (hx : mem x X) : mem (Real.exp x) (DI.exp X) := by
  constructor
  · intro l hl
    simp only [DI.exp] at hl
    split at hl
    · rename_i a ha
      exact le_trans ((mem_expPt a).1 l hl) (Real.exp_le_exp.2 (hx.1 a ha))
    · simp only [Option.some.injEq] at hl; subst hl; rw [val_zero]; exact (Real.exp_pos x).le
  · intro u hu
    simp only [DI.exp] at hu
    split at hu
    · rename_i b hb
      exact le_trans (Real.exp_le_exp.2 (hx.2 b hb)) ((mem_expPt b).2 u hu)
    · simp at hu

/-! ### `sin`, `cos` -/

theorem I_pow_mod (m : ℕ) : Complex.I ^ m = Complex.I ^ (m % 4) := by
  conv_lhs => rw [← Nat.mod_add_div m 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, mul_one]

theorem cosCoef_eq (m : ℕ) :
    ((Interval128.Dy.cosCoef m : ℚ) : ℝ) = (Complex.I ^ m).re / m.factorial := by
  rw [I_pow_mod]
  simp only [Interval128.Dy.cosCoef, fact_eq]
  have h4 : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases (m % 4) <;> simp [pow_succ]

theorem sinCoef_eq (m : ℕ) :
    ((Interval128.Dy.sinCoef m : ℚ) : ℝ) = (Complex.I ^ m).im / m.factorial := by
  rw [I_pow_mod]
  simp only [Interval128.Dy.sinCoef, fact_eq]
  have h4 : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases (m % 4) <;> simp [pow_succ]

theorem trig_sum (y : ℝ) (n : ℕ) :
    ∑ m ∈ range n, ((y : ℂ) * Complex.I) ^ m / m.factorial =
      ∑ m ∈ range n, (((y ^ m / m.factorial : ℝ)) : ℂ) * Complex.I ^ m := by
  apply sum_congr rfl; intro m _
  push_cast; ring

theorem exp_I_re (y : ℝ) : (Complex.exp ((y : ℂ) * Complex.I)).re = Real.cos y := by
  rw [Complex.exp_mul_I]; simp [Complex.cos_ofReal_re, Complex.sin_ofReal_im]

theorem exp_I_im (y : ℝ) : (Complex.exp ((y : ℂ) * Complex.I)).im = Real.sin y := by
  rw [Complex.exp_mul_I]; simp [Complex.sin_ofReal_re, Complex.cos_ofReal_im]

theorem cos_sum_re (y : ℝ) (n : ℕ) :
    (∑ m ∈ range n, (((y ^ m / m.factorial : ℝ)) : ℂ) * Complex.I ^ m).re =
      polyR (Interval128.Dy.coefs Interval128.Dy.cosCoef 0 n) y := by
  rw [Complex.re_sum, polyR_coefs]
  apply sum_congr rfl; intro m _
  rw [Complex.re_ofReal_mul, zero_add, cosCoef_eq]; ring

theorem sin_sum_im (y : ℝ) (n : ℕ) :
    (∑ m ∈ range n, (((y ^ m / m.factorial : ℝ)) : ℂ) * Complex.I ^ m).im =
      polyR (Interval128.Dy.coefs Interval128.Dy.sinCoef 0 n) y := by
  rw [Complex.im_sum, polyR_coefs]
  apply sum_congr rfl; intro m _
  rw [Complex.im_ofReal_mul, zero_add, sinCoef_eq]; ring

theorem cos_taylor_bound {y : ℝ} (hy : |y| ≤ 1) (n : ℕ) (hn : 0 < n) :
    |Real.cos y - polyR (Interval128.Dy.coefs Interval128.Dy.cosCoef 0 n) y| ≤
      |y| ^ n * ((n.succ : ℝ) / (n.factorial * n)) := by
  have hz : ‖(y : ℂ) * Complex.I‖ = |y| := by simp
  have hb := Complex.exp_bound (x := (y : ℂ) * Complex.I) (by rw [hz]; exact hy) hn
  rw [hz, trig_sum] at hb
  have hre := Complex.abs_re_le_norm
    (Complex.exp ((y : ℂ) * Complex.I) - ∑ m ∈ range n, ((y : ℂ) * Complex.I) ^ m / m.factorial)
  rw [Complex.sub_re, trig_sum, exp_I_re, cos_sum_re] at hre
  refine le_trans hre (le_trans hb (le_of_eq ?_))
  field_simp

theorem sin_taylor_bound {y : ℝ} (hy : |y| ≤ 1) (n : ℕ) (hn : 0 < n) :
    |Real.sin y - polyR (Interval128.Dy.coefs Interval128.Dy.sinCoef 0 n) y| ≤
      |y| ^ n * ((n.succ : ℝ) / (n.factorial * n)) := by
  have hz : ‖(y : ℂ) * Complex.I‖ = |y| := by simp
  have hb := Complex.exp_bound (x := (y : ℂ) * Complex.I) (by rw [hz]; exact hy) hn
  rw [hz, trig_sum] at hb
  have him := Complex.abs_im_le_norm
    (Complex.exp ((y : ℂ) * Complex.I) - ∑ m ∈ range n, ((y : ℂ) * Complex.I) ^ m / m.factorial)
  rw [Complex.sub_im, trig_sum, exp_I_im, sin_sum_im] at him
  refine le_trans him (le_trans hb (le_of_eq ?_))
  field_simp

theorem mem_dblIter : ∀ (s : ℕ) {S C : DI} {t : ℝ}, mem (Real.sin t) S → mem (Real.cos t) C →
    mem (Real.sin (t * (2 : ℝ) ^ s)) (Interval128.Dy.dblIter s (S, C)).1 ∧
      mem (Real.cos (t * (2 : ℝ) ^ s)) (Interval128.Dy.dblIter s (S, C)).2 := by
  intro s
  induction s with
  | zero => intro S C t hs hc; simpa [Interval128.Dy.dblIter] using And.intro hs hc
  | succ n ih =>
    intro S C t hs hc
    simp only [Interval128.Dy.dblIter]
    have h1 : mem (Real.sin (t * 2)) (DI.scale 1 (DI.mul S C)) := by
      have := mem_scale 1 (mem_mul hs hc)
      rw [mul_comm t 2, Real.sin_two_mul]; convert this using 1; simp; ring
    have h2 : mem (Real.cos (t * 2)) (DI.sub (DI.mul C C) (DI.mul S S)) := by
      rw [mul_comm t 2, Real.cos_two_mul', sq, sq]; exact mem_sub (mem_mul hc hc) (mem_mul hs hs)
    have := ih h1 h2
    rwa [mul_assoc, ← pow_succ'] at this

theorem mem_sinCosPt (d : Dy) : mem (Real.sin (val d)) (Interval128.Dy.sinCosPt d).1 ∧
    mem (Real.cos (val d)) (Interval128.Dy.sinCosPt d).2 := by
  unfold Interval128.Dy.sinCosPt
  dsimp only
  split_ifs with h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have hy := small_abs h.1
    have hy1 : |val ⟨d.m, d.e - (Interval128.Dy.halvings d : ℤ)⟩| ≤ 1 := by linarith
    have hs := mem_taylor (Interval128.Dy.coefs Interval128.Dy.sinCoef 0 Interval128.Dy.nT) _
      (le_trans (sin_taylor_bound hy1 _ nT_pos) (remT_bound hy))
    have hc := mem_taylor (Interval128.Dy.coefs Interval128.Dy.cosCoef 0 Interval128.Dy.nT) _
      (le_trans (cos_taylor_bound hy1 _ nT_pos) (remT_bound hy))
    have := mem_dblIter (Interval128.Dy.halvings d) hs hc
    rwa [val_halve] at this
  · exact ⟨mem_whole _, mem_whole _⟩

theorem val_max_cases (a b : Dy) : val (Interval128.Dy.max a b) = val a ∨ val (Interval128.Dy.max a b) = val b := by
  unfold Interval128.Dy.max; split_ifs <;> simp

theorem val_min_cases (a b : Dy) : val (Interval128.Dy.min a b) = val a ∨ val (Interval128.Dy.min a b) = val b := by
  unfold Interval128.Dy.min; split_ifs <;> simp

theorem val_negOne : val Interval128.Dy.negOne = -1 := by simp [val, Interval128.Dy.negOne]
theorem val_one : val Interval128.Dy.one = 1 := by simp [val, Interval128.Dy.one]

theorem mem_clamp1 {X : DI} {x : ℝ} (hx : mem x X) (h1 : -1 ≤ x) (h2 : x ≤ 1) :
    mem x (DI.clamp1 X) := by
  constructor
  · rintro l ⟨⟩
    split
    · rename_i a ha
      rcases val_max_cases a Interval128.Dy.negOne with h | h <;> rw [h]
      · exact hx.1 a ha
      · rw [val_negOne]; exact h1
    · rw [val_negOne]; exact h1
  · rintro u ⟨⟩
    split
    · rename_i b hb
      rcases val_min_cases b Interval128.Dy.one with h | h <;> rw [h]
      · exact hx.2 b hb
      · rw [val_one]; exact h2
    · rw [val_one]; exact h2

theorem radius_bound {a b : Dy} (c : Dy) {x : ℝ} (ha : val a ≤ x) (hb : x ≤ val b) :
    |x - val c| ≤ val (Interval128.Dy.radius a b c) := by
  unfold Interval128.Dy.radius
  have h1 := dle_max_left (Interval128.Dy.addX b (Interval128.Dy.neg c)) (Interval128.Dy.addX c (Interval128.Dy.neg a))
  have h2 := dle_max_right (Interval128.Dy.addX b (Interval128.Dy.neg c)) (Interval128.Dy.addX c (Interval128.Dy.neg a))
  rw [val_addX, val_neg] at h1 h2
  rw [abs_le]; constructor <;> linarith

/-- `DI.sinCos` with the point evaluator abstracted. -/
def scG (P : Dy → DI) (X : DI) : DI :=
  match X.lo, X.hi with
  | some a, some b =>
    DI.clamp1 (DI.add (P (Interval128.Dy.centre a b))
      ⟨some (Interval128.Dy.neg (Interval128.Dy.radius a b (Interval128.Dy.centre a b))),
       some (Interval128.Dy.radius a b (Interval128.Dy.centre a b))⟩)
  | _, _ => DI.clamp1 DI.whole

theorem mem_scG {f : ℝ → ℝ} (hb : ∀ t, -1 ≤ f t ∧ f t ≤ 1) (hL : ∀ s t, |f s - f t| ≤ |s - t|)
    (P : Dy → DI) (hP : ∀ d, mem (f (val d)) (P d)) {X : DI} {x : ℝ} (hx : mem x X) :
    mem (f x) (scG P X) := by
  unfold scG
  split
  · rename_i a b ha hb'
    apply mem_clamp1 _ (hb x).1 (hb x).2
    set c := Interval128.Dy.centre a b
    have hr := radius_bound c (hx.1 a ha) (hx.2 b hb')
    have hL' := le_trans (hL x (val c)) hr
    have hpm : mem (f x - f (val c))
        ⟨some (Interval128.Dy.neg (Interval128.Dy.radius a b c)), some (Interval128.Dy.radius a b c)⟩ := by
      have := abs_le.1 hL'
      exact ⟨by rintro l ⟨⟩; rw [val_neg]; linarith, by rintro u ⟨⟩; linarith⟩
    have := mem_add (hP c) hpm
    rwa [add_sub_cancel] at this
  · exact mem_clamp1 (mem_whole _) (hb x).1 (hb x).2

theorem mem_sin {X : DI} {x : ℝ} (hx : mem x X) : mem (Real.sin x) (DI.sinCos false X) := by
  have : DI.sinCos false X = scG (fun c => (Interval128.Dy.sinCosPt c).1) X := by
    unfold DI.sinCos scG; rfl
  rw [this]
  exact mem_scG (fun t => ⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩) Real.abs_sin_sub_sin_le _
    (fun d => (mem_sinCosPt d).1) hx

theorem mem_cos {X : DI} {x : ℝ} (hx : mem x X) : mem (Real.cos x) (DI.sinCos true X) := by
  have : DI.sinCos true X = scG (fun c => (Interval128.Dy.sinCosPt c).2) X := by
    unfold DI.sinCos scG; rfl
  rw [this]
  exact mem_scG (fun t => ⟨Real.neg_one_le_cos t, Real.cos_le_one t⟩) Real.abs_cos_sub_cos_le _
    (fun d => (mem_sinCosPt d).2) hx

/-! ### `log` -/

theorem logCoef_sum (u : ℝ) (n : ℕ) :
    u * polyR (Interval128.Dy.coefs Interval128.Dy.logCoef 0 n) u =
      ∑ i ∈ range n, u ^ (i + 1) / (i + 1) := by
  rw [polyR_coefs, mul_sum]
  apply sum_congr rfl; intro m _
  simp only [Interval128.Dy.logCoef, zero_add]; push_cast
  rw [pow_succ]; field_simp

theorem log_taylor (w : Dy) (hu : |val (Interval128.Dy.addX Interval128.Dy.one (Interval128.Dy.neg w))| ≤ 1 / 64) :
    mem (Real.log (val w)) (Interval128.Dy.logSer w) := by
  unfold Interval128.Dy.logSer
  dsimp only
  set u := Interval128.Dy.addX Interval128.Dy.one (Interval128.Dy.neg w)
  have hw : val w = 1 - val u := by
    simp only [u, val_addX, val_neg, val_one]; ring
  have hu' : |val u| < 1 := by linarith
  have hb := Real.abs_log_sub_add_sum_range_le hu' Interval128.Dy.nL
  rw [← logCoef_sum, ← hw] at hb
  have hR : |val u| ^ (Interval128.Dy.nL + 1) / (1 - |val u|) ≤ ((Interval128.Dy.remL : ℚ) : ℝ) := by
    have h0 : 0 ≤ |val u| := abs_nonneg _
    have hp : |val u| ^ (Interval128.Dy.nL + 1) ≤ (1 / 64 : ℝ) ^ (Interval128.Dy.nL + 1) :=
      pow_le_pow_left₀ h0 hu _
    have hd : (1 / 2 : ℝ) ≤ 1 - |val u| := by linarith
    rw [div_le_iff₀ (by linarith)]
    simp only [Interval128.Dy.remL]; push_cast
    have : (0 : ℝ) ≤ (1 / 64) ^ (Interval128.Dy.nL + 1) := by positivity
    nlinarith
  have hdec : decide (-(1 / 64) ≤ Interval128.Dy.toRat u ∧ Interval128.Dy.toRat u ≤ 1 / 64) = true := by
    rw [decide_eq_true_eq]
    have := abs_le.1 hu
    rw [← toRat_val] at this
    refine ⟨(Rat.cast_le (K := ℝ)).1 ?_, (Rat.cast_le (K := ℝ)).1 ?_⟩ <;> push_cast <;> linarith [this.1, this.2]
  rw [if_pos hdec]
  have hneg := mem_neg (mem_mulPt u (mem_horner (Interval128.Dy.coefs Interval128.Dy.logCoef 0
    Interval128.Dy.nL) u))
  have := mem_add hneg (mem_pm (le_trans hb hR))
  convert this using 1; ring

theorem log_taylor' (w : Dy) : ∀ Y, Interval128.Dy.logSer w = Y →
    (Y.lo.isSome ∨ Y.hi.isSome) → mem (Real.log (val w)) Y := by
  intro Y hY hs
  subst hY
  unfold Interval128.Dy.logSer at hs ⊢
  dsimp only at hs ⊢
  split_ifs at hs ⊢ with h
  · have := of_decide_eq_true h
    have hu : |val (Interval128.Dy.addX Interval128.Dy.one (Interval128.Dy.neg w))| ≤ 1 / 64 := by
      rw [← toRat_val, abs_le]
      have t1 := (Rat.cast_le (K := ℝ)).2 this.1
      have t2 := (Rat.cast_le (K := ℝ)).2 this.2
      push_cast at t1 t2
      exact ⟨t1, t2⟩
    have := log_taylor w hu
    unfold Interval128.Dy.logSer at this
    dsimp only at this
    rwa [if_pos h] at this
  · simp [DI.whole] at hs

theorem mem_sqrtIter : ∀ (j : ℕ) {X : DI} {x : ℝ}, mem x X →
    mem (Real.sqrt^[j] x) (Interval128.Dy.sqrtIter j X) := by
  intro j
  induction j with
  | zero => intro X x h; simpa [Interval128.Dy.sqrtIter] using h
  | succ n ih =>
    intro X x h
    simp only [Interval128.Dy.sqrtIter, Function.iterate_succ_apply]
    exact ih (mem_sqrt h)

theorem log_sqrt_iter : ∀ (j : ℕ) {x : ℝ}, 0 ≤ x →
    Real.log x = (2 : ℝ) ^ j * Real.log (Real.sqrt^[j] x) ∧ 0 ≤ Real.sqrt^[j] x := by
  intro j
  induction j with
  | zero => intro x hx; simp [hx]
  | succ n ih =>
    intro x hx
    simp only [Function.iterate_succ_apply]
    obtain ⟨h1, h2⟩ := ih (Real.sqrt_nonneg x)
    refine ⟨?_, h2⟩
    have : Real.log x = 2 * Real.log (Real.sqrt x) := by rw [Real.log_sqrt hx]; ring
    rw [this, h1, pow_succ]; ring

theorem iter_pos : ∀ (j : ℕ) {x : ℝ}, 0 ≤ x → 0 < Real.sqrt^[j] x → 0 < x := by
  intro j
  induction j with
  | zero => intro x _ h; simpa using h
  | succ n ih =>
    intro x hx h
    simp only [Function.iterate_succ_apply] at h
    exact Real.sqrt_pos.1 (ih (Real.sqrt_nonneg x) h)

theorem iter_zero (k : ℕ) : Real.sqrt^[k] 0 = 0 := by
  induction k with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, Real.sqrt_zero]

theorem logLo_spec {d : Dy} {l : Dy} (h : Interval128.Dy.logLo d = some l) :
    0 < val d ∧ val l ≤ Real.log (val d) := by
  unfold Interval128.Dy.logLo at h
  dsimp only at h
  set j := Interval128.Dy.roots d
  split at h
  · rename_i w hw
    split_ifs at h with hpos
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨l0, hl0, rfl⟩ := h
    have hm := mem_sqrtIter j (mem_pt d)
    have hwle := hm.1 w hw
    have hwpos : 0 < val w := (val_pos_iff w).2 hpos
    by_cases hd : 0 ≤ val d
    · have hdpos := iter_pos j hd (lt_of_lt_of_le hwpos hwle)
      refine ⟨hdpos, ?_⟩
      obtain ⟨e1, _⟩ := log_sqrt_iter j hd
      have hser := log_taylor' w _ rfl (by rw [hl0]; simp)
      have hl := hser.1 l0 hl0
      rw [val_scale, e1]
      have hlog : Real.log (val w) ≤ Real.log (Real.sqrt^[j] (val d)) :=
        Real.log_le_log hwpos hwle
      have : val l0 ≤ Real.log (Real.sqrt^[j] (val d)) := le_trans hl hlog
      rw [zpow_natCast, mul_comm ((2 : ℝ) ^ j)]
      exact mul_le_mul_of_nonneg_right this (by positivity)
    · exfalso
      have hd' : val d < 0 := lt_of_not_ge hd
      have hz : Real.sqrt^[j] (val d) ≤ 0 := by
        cases j with
        | zero => simpa using hd'.le
        | succ n =>
          simp only [Function.iterate_succ_apply, Real.sqrt_eq_zero'.2 hd'.le]
          rw [iter_zero]
      linarith
  · simp at h

theorem logHi_spec {d : Dy} {u : Dy} (hd : 0 < val d) (h : Interval128.Dy.logHi d = some u) :
    Real.log (val d) ≤ val u := by
  unfold Interval128.Dy.logHi at h
  dsimp only at h
  set j := Interval128.Dy.roots d
  split at h
  · rename_i w hw
    split_ifs at h with hpos
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨u0, hu0, rfl⟩ := h
    have hm := mem_sqrtIter j (mem_pt d)
    have hwge := hm.2 w hw
    obtain ⟨e1, hnn⟩ := log_sqrt_iter j hd.le
    have hipos : 0 < Real.sqrt^[j] (val d) := by
      clear * - hd
      induction j with
      | zero => simpa using hd
      | succ n ih => simp only [Function.iterate_succ_apply']; exact Real.sqrt_pos.2 ih
    have hser := log_taylor' w _ rfl (by rw [hu0]; simp)
    have hu := hser.2 u0 hu0
    rw [val_scale, e1]
    have hlog : Real.log (Real.sqrt^[j] (val d)) ≤ Real.log (val w) := Real.log_le_log hipos hwge
    rw [zpow_natCast, mul_comm ((2 : ℝ) ^ j)]
    exact mul_le_mul_of_nonneg_right (le_trans hlog hu) (by positivity)
  · simp at h

theorem mem_log? {X Y : DI} {x : ℝ} (hx : mem x X) (h : DI.log? X = some Y) :
    mem (Real.log x) Y := by
  unfold DI.log? at h
  split at h
  · rename_i a ha
    split_ifs at h with hpos
    simp only [Option.some.injEq] at h; subst h
    have hva : 0 < val a := (val_pos_iff a).2 hpos
    have hxa := hx.1 a ha
    have hx0 : 0 < x := lt_of_lt_of_le hva hxa
    constructor
    · intro l hl
      obtain ⟨_, h2⟩ := logLo_spec hl
      exact le_trans h2 (Real.log_le_log hva hxa)
    · intro u hu
      simp only [Option.bind_eq_some_iff] at hu
      obtain ⟨b, hb, hu⟩ := hu
      have hxb := hx.2 b hb
      have hvb : 0 < val b := lt_of_lt_of_le hx0 hxb
      exact le_trans (Real.log_le_log hx0 hxb) (logHi_spec hvb hu)
  · simp at h

theorem mem_logConst {q : ℚ} (hq : 0 < q) : mem (Real.log q) (DI.logConst q) := by
  constructor
  · intro l hl
    obtain ⟨h1, h2⟩ := logLo_spec hl
    exact le_trans h2 (Real.log_le_log h1 (val_ofRatDn q))
  · intro u hu
    have h0 : (0 : ℝ) < q := by exact_mod_cast hq
    have hle := val_ofRatUp q
    exact le_trans (Real.log_le_log h0 hle) (logHi_spec (lt_of_lt_of_le h0 hle) hu)

/-! ### Hyperbolic functions -/

theorem sinh_pt (d : Dy) : mem (Real.sinh (val d))
    (DI.scale (-1) (DI.sub (Interval128.Dy.expPt d) (DI.inv (Interval128.Dy.expPt d)))) := by
  have := mem_scale (-1) (mem_sub (mem_expPt d) (mem_inv (mem_expPt d)))
  convert this using 1
  rw [Real.sinh_eq, Real.exp_neg, zpow_neg_one]; ring

theorem cosh_pt (d : Dy) : mem (Real.cosh (val d))
    (DI.scale (-1) (DI.add (Interval128.Dy.expPt d) (DI.inv (Interval128.Dy.expPt d)))) := by
  have := mem_scale (-1) (mem_add (mem_expPt d) (mem_inv (mem_expPt d)))
  convert this using 1
  rw [Real.cosh_eq, Real.exp_neg, zpow_neg_one]; ring

theorem sinhCoef_sum (y : ℝ) (n : ℕ) :
    polyR (Interval128.Dy.coefs Interval128.Dy.sinhCoef 0 n) y =
      ((∑ m ∈ range n, y ^ m / m.factorial) - ∑ m ∈ range n, (-y) ^ m / m.factorial) / 2 := by
  rw [polyR_coefs, ← sum_sub_distrib, sum_div]
  apply sum_congr rfl; intro m _
  simp only [Interval128.Dy.sinhCoef, zero_add, fact_eq]
  rcases Nat.even_or_odd m with h | h
  · have h2 : m % 2 = 0 := Nat.even_iff.1 h
    rw [if_neg (by omega), h.neg_pow]; push_cast; ring
  · have h2 : m % 2 = 1 := Nat.odd_iff.1 h
    rw [if_pos h2, h.neg_pow]; push_cast; ring

theorem sinh_taylor_bound (y : ℝ) (hy : |y| ≤ 1 / 256) :
    |Real.sinh y - polyR (Interval128.Dy.coefs Interval128.Dy.sinhCoef 0 Interval128.Dy.nT) y| ≤
      ((Interval128.Dy.remT : ℚ) : ℝ) := by
  have hy' : |-y| ≤ 1 / 256 := by rwa [abs_neg]
  have h1 := le_trans (Real.exp_bound (by linarith) nT_pos) (remT_bound hy)
  have h2 := le_trans (Real.exp_bound (by linarith) nT_pos) (remT_bound hy')
  rw [sinhCoef_sum, Real.sinh_eq]
  set A := ∑ m ∈ range Interval128.Dy.nT, y ^ m / m.factorial
  set B := ∑ m ∈ range Interval128.Dy.nT, (-y) ^ m / m.factorial
  have : Real.exp y / 2 - Real.exp (-y) / 2 - (A - B) / 2 =
      ((Real.exp y - A) - (Real.exp (-y) - B)) / 2 := by ring
  rw [show (Real.exp y - Real.exp (-y)) / 2 = Real.exp y / 2 - Real.exp (-y) / 2 by ring, this,
    abs_div, abs_two]
  have := abs_sub (Real.exp y - A) (Real.exp (-y) - B)
  linarith

theorem mem_sinhPt (d : Dy) : mem (Real.sinh (val d)) (Interval128.Dy.sinhPt d) := by
  unfold Interval128.Dy.sinhPt
  split_ifs with h
  · exact mem_taylor _ d (sinh_taylor_bound _ (small_abs h))
  · exact sinh_pt d

theorem mem_coshPt (d : Dy) : mem (Real.cosh (val d)) (Interval128.Dy.coshPt d) := cosh_pt d

theorem mem_sinh {X : DI} {x : ℝ} (hx : mem x X) : mem (Real.sinh x) (DI.sinh X) := by
  constructor
  · intro l hl
    simp only [DI.sinh, Option.bind_eq_some_iff] at hl
    obtain ⟨a, ha, hl⟩ := hl
    exact le_trans ((mem_sinhPt a).1 l hl) (Real.sinh_le_sinh.2 (hx.1 a ha))
  · intro u hu
    simp only [DI.sinh, Option.bind_eq_some_iff] at hu
    obtain ⟨b, hb, hu⟩ := hu
    exact le_trans (Real.sinh_le_sinh.2 (hx.2 b hb)) ((mem_sinhPt b).2 u hu)

theorem mem_cosh {X : DI} {x : ℝ} (hx : mem x X) : mem (Real.cosh x) (DI.cosh X) := by
  have hA := mem_abs hx
  constructor
  · intro l hl
    simp only [DI.cosh] at hl
    split at hl
    · rename_i a ha
      split_ifs at hl with hpos
      · have h0 : 0 ≤ val a := (val_nonneg_iff a).2 hpos
        have hle := hA.1 a ha
        refine le_trans ((mem_coshPt a).1 l hl) (Real.cosh_le_cosh.2 ?_)
        rw [abs_of_nonneg h0]; exact hle
      · simp only [Option.some.injEq] at hl; subst hl; rw [val_one]; exact Real.one_le_cosh x
    · simp only [Option.some.injEq] at hl; subst hl; rw [val_one]; exact Real.one_le_cosh x
  · intro u hu
    simp only [DI.cosh, Option.bind_eq_some_iff] at hu
    obtain ⟨b, hb, hu⟩ := hu
    have hle := hA.2 b hb
    refine le_trans (Real.cosh_le_cosh.2 ?_) ((mem_coshPt b).2 u hu)
    rw [abs_of_nonneg (le_trans (abs_nonneg x) hle)]; exact hle

theorem tanh_eq' (x : ℝ) : Real.tanh x = 1 - 2 * (Real.exp (x * 2 ^ (1 : ℤ)) + 1)⁻¹ := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, zpow_one]
  have h1 : Real.exp (x * 2) = Real.exp x * Real.exp x := by rw [mul_two, Real.exp_add]
  have h2 : Real.exp (-x) = (Real.exp x)⁻¹ := Real.exp_neg x
  have hp := Real.exp_pos x
  rw [h1, h2]
  field_simp
  ring

theorem tanh_le_tanh {x y : ℝ} (h : x ≤ y) : Real.tanh x ≤ Real.tanh y := by
  rw [tanh_eq', tanh_eq']
  have h2 : Real.exp (x * 2 ^ (1 : ℤ)) ≤ Real.exp (y * 2 ^ (1 : ℤ)) :=
    Real.exp_le_exp.2 (by rw [zpow_one]; linarith)
  have hp := Real.exp_pos (x * 2 ^ (1 : ℤ))
  gcongr

theorem mem_tanhPt (d : Dy) : mem (Real.tanh (val d)) (Interval128.Dy.tanhPt d) := by
  unfold Interval128.Dy.tanhPt
  split_ifs with h
  · rw [Real.tanh_eq_sinh_div_cosh]; exact mem_div (mem_sinhPt d) (mem_coshPt d)
  · rw [tanh_eq', ← val_scale]
    exact mem_sub (mem_ofRat' 1 (by simp)) (mem_mul (mem_ofRat' 2 (by simp)) (mem_inv
      (mem_add (mem_expPt _) (mem_ofRat' 1 (by simp)))))

theorem mem_tanh {X : DI} {x : ℝ} (hx : mem x X) : mem (Real.tanh x) (DI.tanh X) := by
  unfold DI.tanh
  apply mem_clamp1 _ (Real.neg_one_lt_tanh x).le (Real.tanh_lt_one x).le
  constructor
  · intro l hl
    simp only [Option.bind_eq_some_iff] at hl
    obtain ⟨a, ha, hl⟩ := hl
    exact le_trans ((mem_tanhPt a).1 l hl) (tanh_le_tanh (hx.1 a ha))
  · intro u hu
    simp only [Option.bind_eq_some_iff] at hu
    obtain ⟨b, hb, hu⟩ := hu
    exact le_trans (tanh_le_tanh (hx.2 b hb)) ((mem_tanhPt b).2 u hu)

end RealFP.I128Q
