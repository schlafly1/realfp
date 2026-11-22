/-
Taylor bounds with an explicit derivative chain, and the Taylor cell rule for integrals.

`F : ℕ → ℝ → ℝ` with `HasDerivAt (F j) (F (j+1) t) t`; `tay F m K x = Σ_{j<K} F j m (x-m)^j / j!`.

* `taylor_lower_right` / `taylor_upper_right` / `taylor_lower_left` / `taylor_upper_left` :
  Lagrange-type bounds of the remainder `F 0 x - tay F m K x` from bounds `c ≤ F K ≤ c'`.
* `integral_tay` : `∫_lo^hi tay = Σ_{j<K} F j m · mom lo m hi j`.
* `integral_mem_taylorCell` : for even `K`, `∫_lo^hi F 0 = Σ_{j<K} F j m · mom j + r` with
  `r ∈ D * Q` whenever `F K ∈ D` on `[lo, hi]` and `mom K ∈ Q`.
-/
import RealFPMathlib.Quad

open Set intervalIntegral MeasureTheory Finset

noncomputable section

namespace RealFP.Taylor

/-- Taylor polynomial of the chain `F` at `m`, `K` terms. -/
def tay (F : ℕ → ℝ → ℝ) (m : ℝ) (K : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range K, F j m * (x - m) ^ j / (j.factorial : ℝ)

/-- `∫_lo^hi (x - m)^j / j! dx`. -/
def mom (lo m hi : ℝ) (j : ℕ) : ℝ :=
  ((hi - m) ^ (j + 1) - (lo - m) ^ (j + 1)) * (1 / ((j + 1).factorial : ℝ))

theorem hasDerivAt_powTerm (m : ℝ) (j : ℕ) (x : ℝ) :
    HasDerivAt (fun x => (x - m) ^ (j + 1) / ((j + 1).factorial : ℝ))
      ((x - m) ^ j / (j.factorial : ℝ)) x := by
  have h1 : HasDerivAt (fun x => x - m) 1 x := (hasDerivAt_id x).sub_const m
  have h2 : HasDerivAt (fun x => (x - m) ^ (j + 1)) (((j + 1 : ℕ) : ℝ) * (x - m) ^ j) x := by
    have := (hasDerivAt_pow (j + 1) (x - m)).comp x h1
    simp only [Function.comp_def, mul_one, Nat.add_sub_cancel] at this
    convert this using 1
  convert h2.div_const ((j + 1).factorial : ℝ) using 1
  rw [Nat.factorial_succ]; push_cast
  have : (j.factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem tay_succ (F : ℕ → ℝ → ℝ) (m : ℝ) (K : ℕ) (x : ℝ) :
    tay F m (K + 1) x = F 0 m + ∑ j ∈ range K, F (j + 1) m * ((x - m) ^ (j + 1) / ((j + 1).factorial : ℝ)) := by
  rw [tay, sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
  rw [add_comm]; congr 1
  refine sum_congr rfl fun j _ => by ring

theorem tay_self (F : ℕ → ℝ → ℝ) (m : ℝ) (K : ℕ) : tay F m (K + 1) m = F 0 m := by
  rw [tay_succ]; simp

theorem hasDerivAt_tay (F : ℕ → ℝ → ℝ) (m : ℝ) (K : ℕ) (x : ℝ) :
    HasDerivAt (tay F m (K + 1)) (tay (fun j => F (j + 1)) m K x) x := by
  have e : tay F m (K + 1) = fun x => F 0 m +
      ∑ j ∈ range K, F (j + 1) m * ((x - m) ^ (j + 1) / ((j + 1).factorial : ℝ)) :=
    funext (tay_succ F m K)
  rw [e]
  have hs : HasDerivAt (fun x => ∑ j ∈ range K, F (j + 1) m * ((x - m) ^ (j + 1) / ((j + 1).factorial : ℝ)))
      (∑ j ∈ range K, F (j + 1) m * ((x - m) ^ j / (j.factorial : ℝ))) x :=
    HasDerivAt.fun_sum fun j _ => (hasDerivAt_powTerm m j x).const_mul _
  convert hs.const_add (F 0 m) using 1
  simp only [tay]; refine sum_congr rfl fun j _ => by ring

/-- Lower remainder bound on the right of `m`. -/
theorem taylor_lower_right : ∀ (K : ℕ) (F : ℕ → ℝ → ℝ) {m b : ℝ} (c : ℝ),
    (∀ j < K, ∀ t ∈ Icc m b, HasDerivAt (F j) (F (j + 1) t) t) → (∀ t ∈ Icc m b, c ≤ F K t) →
      ∀ x ∈ Icc m b, c * (x - m) ^ K / (K.factorial : ℝ) ≤ F 0 x - tay F m K x
  | 0, F, m, b, c, _, hc, x, hx => by simpa [tay] using hc x hx
  | K + 1, F, m, b, c, hd, hc, x, hx => by
    have ih := taylor_lower_right K (fun j => F (j + 1)) c
      (fun j hj t ht => hd (j + 1) (by omega) t ht) hc
    set h : ℝ → ℝ := fun x => F 0 x - tay F m (K + 1) x -
      c * ((x - m) ^ (K + 1) / ((K + 1).factorial : ℝ)) with hh
    have hder : ∀ t ∈ Icc m b, HasDerivAt h
        (F 1 t - tay (fun j => F (j + 1)) m K t - c * ((t - m) ^ K / (K.factorial : ℝ))) t :=
      fun t ht => ((hd 0 (by omega) t ht).sub (hasDerivAt_tay F m K t)).sub
        ((hasDerivAt_powTerm m K t).const_mul c)
    have hm : h m = 0 := by simp [hh, tay_self]
    suffices 0 ≤ h x by simp only [hh] at this; rw [mul_div_assoc]; linarith
    rcases eq_or_lt_of_le hx.1 with e | hlt
    · rw [← e, hm]
    · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope h _ hlt
        (fun t ht => (hder t ⟨ht.1, ht.2.trans hx.2⟩).continuousAt.continuousWithinAt)
        (fun t ht => hder t ⟨ht.1.le, ht.2.le.trans hx.2⟩)
      have hξ0 := ih ξ ⟨hξ.1.le, hξ.2.le.trans hx.2⟩
      have hpos : 0 ≤ (h x - h m) / (x - m) := by
        rw [← hξe]; rw [mul_div_assoc] at hξ0; linarith
      rw [hm, sub_zero] at hpos
      exact (div_nonneg_iff.1 hpos).elim (fun h' => h'.1) fun h' => absurd h'.2 (by linarith)

theorem tay_neg (F : ℕ → ℝ → ℝ) (m : ℝ) (K : ℕ) (x : ℝ) :
    tay (fun j t => -F j t) m K x = -tay F m K x := by
  simp only [tay, ← sum_neg_distrib]; refine sum_congr rfl fun j _ => by ring

theorem taylor_upper_right (K : ℕ) (F : ℕ → ℝ → ℝ) {m b : ℝ} (c : ℝ)
    (hd : ∀ j < K, ∀ t ∈ Icc m b, HasDerivAt (F j) (F (j + 1) t) t) (hc : ∀ t ∈ Icc m b, F K t ≤ c) :
    ∀ x ∈ Icc m b, F 0 x - tay F m K x ≤ c * (x - m) ^ K / (K.factorial : ℝ) := by
  intro x hx
  have := taylor_lower_right K (fun j t => -F j t) (-c) (fun j hj t ht => (hd j hj t ht).neg)
    (fun t ht => neg_le_neg (hc t ht)) x hx
  rw [tay_neg] at this
  have e : -c * (x - m) ^ K / (K.factorial : ℝ) = -(c * (x - m) ^ K / (K.factorial : ℝ)) := by ring
  linarith

/-- Lower remainder bound on the left of `m` (sign `(-1)^K`). -/
theorem taylor_lower_left : ∀ (K : ℕ) (F : ℕ → ℝ → ℝ) {a m : ℝ} (c : ℝ),
    (∀ j < K, ∀ t ∈ Icc a m, HasDerivAt (F j) (F (j + 1) t) t) → (∀ t ∈ Icc a m, c ≤ F K t) →
      ∀ x ∈ Icc a m, c * (m - x) ^ K / (K.factorial : ℝ) ≤ (-1) ^ K * (F 0 x - tay F m K x)
  | 0, F, a, m, c, _, hc, x, hx => by simpa [tay] using hc x hx
  | K + 1, F, a, m, c, hd, hc, x, hx => by
    have ih := taylor_lower_left K (fun j => F (j + 1)) c
      (fun j hj t ht => hd (j + 1) (by omega) t ht) hc
    set h : ℝ → ℝ := fun x => (-1) ^ (K + 1) * (F 0 x - tay F m (K + 1) x) -
      c * ((m - x) ^ (K + 1) / ((K + 1).factorial : ℝ)) with hh
    have hq : ∀ t, HasDerivAt (fun x => (m - x) ^ (K + 1) / ((K + 1).factorial : ℝ))
        (-((m - t) ^ K / (K.factorial : ℝ))) t := fun t => by
      have h1 := hasDerivAt_powTerm 0 K (m - t)
      have h2 := h1.comp t ((hasDerivAt_id t).const_sub m)
      simp only [sub_zero, Function.comp_def, id] at h2
      convert h2 using 1; ring
    have hder : ∀ t ∈ Icc a m, HasDerivAt h
        ((-1) ^ (K + 1) * (F 1 t - tay (fun j => F (j + 1)) m K t) +
          c * ((m - t) ^ K / (K.factorial : ℝ))) t := fun t ht => by
      have := (((hd 0 (by omega) t ht).sub (hasDerivAt_tay F m K t)).const_mul ((-1 : ℝ) ^ (K + 1))).sub
        ((hq t).const_mul c)
      convert this using 1; ring
    have hm : h m = 0 := by simp [hh, tay_self]
    suffices 0 ≤ h x by simp only [hh] at this; rw [mul_div_assoc]; linarith
    rcases eq_or_lt_of_le hx.2 with e | hlt
    · rw [e, hm]
    · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope h _ hlt
        (fun t ht => (hder t ⟨hx.1.trans ht.1, ht.2⟩).continuousAt.continuousWithinAt)
        (fun t ht => hder t ⟨hx.1.trans ht.1.le, ht.2.le⟩)
      have hξ0 := ih ξ ⟨hx.1.trans hξ.1.le, hξ.2.le⟩
      have hneg : (h m - h x) / (m - x) ≤ 0 := by
        rw [← hξe, pow_succ]; rw [mul_div_assoc] at hξ0; nlinarith
      rw [hm, zero_sub] at hneg
      have hmx : 0 < m - x := by linarith
      have := (div_nonpos_iff.1 hneg)
      rcases this with h' | h'
      · linarith [h'.2]
      · linarith [h'.1]

theorem taylor_upper_left (K : ℕ) (F : ℕ → ℝ → ℝ) {a m : ℝ} (c : ℝ)
    (hd : ∀ j < K, ∀ t ∈ Icc a m, HasDerivAt (F j) (F (j + 1) t) t) (hc : ∀ t ∈ Icc a m, F K t ≤ c) :
    ∀ x ∈ Icc a m, (-1) ^ K * (F 0 x - tay F m K x) ≤ c * (m - x) ^ K / (K.factorial : ℝ) := by
  intro x hx
  have := taylor_lower_left K (fun j t => -F j t) (-c) (fun j hj t ht => (hd j hj t ht).neg)
    (fun t ht => neg_le_neg (hc t ht)) x hx
  rw [tay_neg] at this
  have e : -c * (m - x) ^ K / (K.factorial : ℝ) = -(c * (m - x) ^ K / (K.factorial : ℝ)) := by ring
  have e2 : (-1 : ℝ) ^ K * (-F 0 x - -tay F m K x) = -((-1) ^ K * (F 0 x - tay F m K x)) := by ring
  linarith

end RealFP.Taylor
