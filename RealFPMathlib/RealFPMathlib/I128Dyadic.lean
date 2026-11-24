/-
Soundness of the dyadic `(precision := 128)` checker (`Interval128/Dyadic.lean`) over `ℝ`.

* `val d = d.m * 2 ^ d.e`; `mem x X` says `x` lies between the finite endpoints of `X`.
* `evalQ_sound` — `e.denote xs` lies in `Interval128.Dy.evalQ env e` whenever each `xs[i]` lies in `env[i]`.
* `checkQ_sound`, `prove_le` / `prove_lt` / `prove_ge` / `prove_gt` — what the tactic uses.
-/
import Interval128
import RealFPMathlib.IntervalSound
import RealFPMathlib.I128Prims
import RealFPMathlib.PiBounds

open Interval64 Interval64.KF
open Interval128.Dy (Dy DI)
open Interval64.Spec Interval64Proofs.FloatBits

noncomputable section

namespace RealFP.I128Q

/-! ### Dyadic numbers -/

/-- Value of `m · 2^e`. -/
def val (a : Dy) : ℝ := (a.m : ℝ) * (2 : ℝ) ^ a.e

theorem two_zpow_pos (e : ℤ) : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) e

theorem zpow_add_nat (e : ℤ) (s : ℕ) : (2 : ℝ) ^ (e + (s : ℤ)) = (2 : ℝ) ^ e * (2 : ℝ) ^ s := by
  rw [zpow_add₀ (by norm_num), zpow_natCast]

theorem cast_pow2 (s : ℕ) : (((2 ^ s : ℕ) : ℤ) : ℝ) = (2 : ℝ) ^ s := by
  rw [Int.cast_natCast, Nat.cast_pow, Nat.cast_ofNat]

theorem div_core (m : ℤ) (D : ℕ) (hD : 0 < D) : (((m / (D : ℤ)) : ℤ) : ℝ) * (D : ℝ) ≤ (m : ℝ) := by
  have h := Int.ediv_mul_le m (by exact_mod_cast hD.ne' : (D : ℤ) ≠ 0)
  have h' : (((m / (D : ℤ)) * (D : ℤ) : ℤ) : ℝ) ≤ (m : ℝ) := Int.cast_le.2 h
  rwa [Int.cast_mul, Int.cast_natCast] at h'

theorem rdn_core (m e : ℤ) (s : ℕ) :
    ((m / ((2 ^ s : ℕ) : ℤ) : ℤ) : ℝ) * (2 : ℝ) ^ (e + (s : ℤ)) ≤ (m : ℝ) * (2 : ℝ) ^ e := by
  have h2 : ((m / ((2 ^ s : ℕ) : ℤ) : ℤ) : ℝ) * (2 : ℝ) ^ s ≤ (m : ℝ) := by
    have := div_core m (2 ^ s) (by positivity)
    rwa [show ((2 ^ s : ℕ) : ℝ) = (2 : ℝ) ^ s by norm_num] at this
  rw [zpow_add_nat, mul_comm ((2 : ℝ) ^ e), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h2 (two_zpow_pos e).le

theorem rup_core (m e : ℤ) (s : ℕ) :
    (m : ℝ) * (2 : ℝ) ^ e ≤ ((-((-m) / ((2 ^ s : ℕ) : ℤ)) : ℤ) : ℝ) * (2 : ℝ) ^ (e + (s : ℤ)) := by
  have h := rdn_core (-m) e s
  rw [Int.cast_neg, neg_mul] at h
  rw [Int.cast_neg, neg_mul]
  linarith

theorem val_rdn (m e : ℤ) : val (Interval128.Dy.rdn m e) ≤ (m : ℝ) * (2 : ℝ) ^ e := by
  unfold Interval128.Dy.rdn
  generalize Interval128.Dy.shiftOf m = s
  exact rdn_core m e s

theorem val_rup (m e : ℤ) : (m : ℝ) * (2 : ℝ) ^ e ≤ val (Interval128.Dy.rup m e) := by
  unfold Interval128.Dy.rup
  generalize Interval128.Dy.shiftOf m = s
  exact rup_core m e s

theorem val_rdn' (d : Dy) : val (Interval128.Dy.rdn d.m d.e) ≤ val d := val_rdn d.m d.e
theorem val_rup' (d : Dy) : val d ≤ val (Interval128.Dy.rup d.m d.e) := val_rup d.m d.e

theorem val_neg (a : Dy) : val (Interval128.Dy.neg a) = -val a := by
  simp only [val, Interval128.Dy.neg]; push_cast; ring

theorem val_mulX (a b : Dy) : val (Interval128.Dy.mulX a b) = val a * val b := by
  simp only [val, Interval128.Dy.mulX]; push_cast
  rw [zpow_add₀ (by norm_num)]; ring

theorem val_addX (a b : Dy) : val (Interval128.Dy.addX a b) = val a + val b := by
  unfold Interval128.Dy.addX val
  split_ifs with h
  · have ht : ((b.e - a.e).toNat : ℤ) = b.e - a.e := Int.toNat_of_nonneg (by omega)
    have : (2 : ℝ) ^ b.e = (2 : ℝ) ^ a.e * (2 : ℝ) ^ (b.e - a.e).toNat := by
      rw [← zpow_add_nat, ht]; congr 1; ring
    simp only
    push_cast
    rw [this]; ring
  · have ht : ((a.e - b.e).toNat : ℤ) = a.e - b.e := Int.toNat_of_nonneg (by omega)
    have : (2 : ℝ) ^ a.e = (2 : ℝ) ^ b.e * (2 : ℝ) ^ (a.e - b.e).toNat := by
      rw [← zpow_add_nat, ht]; congr 1; ring
    simp only
    push_cast
    rw [this]; ring

theorem val_nonpos_iff (d : Dy) : val d ≤ 0 ↔ d.m ≤ 0 := by
  have h := two_zpow_pos d.e
  unfold val
  constructor
  · intro hv; by_contra hc
    have : (0 : ℝ) < d.m := by exact_mod_cast (show (0 : ℤ) < d.m by omega)
    nlinarith
  · intro hm
    have : (d.m : ℝ) ≤ 0 := by exact_mod_cast hm
    nlinarith

theorem val_pos_iff (d : Dy) : 0 < val d ↔ 0 < d.m := by
  rw [← not_le, val_nonpos_iff, not_le]

theorem val_neg_iff (d : Dy) : val d < 0 ↔ d.m < 0 := by
  have := val_nonpos_iff (Interval128.Dy.neg d)
  rw [val_neg] at this
  simp only [Interval128.Dy.neg] at this
  constructor
  · intro h; by_contra hc; have := this.2 (by omega); linarith
  · intro h; by_contra hc; have := this.1 (by linarith); omega

theorem val_nonneg_iff (d : Dy) : 0 ≤ val d ↔ 0 ≤ d.m := by
  rw [← not_lt, val_neg_iff, not_lt]

theorem le_iff (a b : Dy) : Interval128.Dy.le a b = true ↔ val a ≤ val b := by
  unfold Interval128.Dy.le
  rw [decide_eq_true_iff, ← val_nonpos_iff, val_addX, val_neg]
  constructor <;> intro h <;> linarith

theorem dmin_le_left (a b : Dy) : val (Interval128.Dy.min a b) ≤ val a := by
  unfold Interval128.Dy.min; split_ifs with h
  · exact le_rfl
  · have := (le_iff a b).not.1 (by simpa using h); linarith

theorem dmin_le_right (a b : Dy) : val (Interval128.Dy.min a b) ≤ val b := by
  unfold Interval128.Dy.min; split_ifs with h
  · exact (le_iff a b).1 h
  · exact le_rfl

theorem dle_max_left (a b : Dy) : val a ≤ val (Interval128.Dy.max a b) := by
  unfold Interval128.Dy.max; split_ifs with h
  · exact (le_iff a b).1 h
  · exact le_rfl

theorem dle_max_right (a b : Dy) : val b ≤ val (Interval128.Dy.max a b) := by
  unfold Interval128.Dy.max; split_ifs with h
  · exact le_rfl
  · have := (le_iff a b).not.1 (by simpa using h); linarith

theorem toRat_val (a : Dy) : ((Interval128.Dy.toRat a : ℚ) : ℝ) = val a := by
  unfold Interval128.Dy.toRat val
  split_ifs with h
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
    rw [hn, Int.toNat_natCast, Rat.cast_intCast, Int.cast_mul, cast_pow2, zpow_natCast]
  · have ht : ((-a.e).toNat : ℤ) = -a.e := Int.toNat_of_nonneg (by omega)
    have : (2 : ℝ) ^ a.e = ((2 : ℝ) ^ (-a.e).toNat)⁻¹ := by
      rw [← zpow_natCast, ht, zpow_neg, inv_inv]
    rw [this, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, Nat.cast_pow, Nat.cast_ofNat,
      div_eq_mul_inv]

theorem val_ofRatDn (q : ℚ) : val (Interval128.Dy.ofRatDn q) ≤ (q : ℝ) := by
  unfold Interval128.Dy.ofRatDn
  generalize Interval128.Dy.prec + Interval128.Dy.bitlen q.den = k
  refine le_trans (val_rdn _ _) ?_
  have h2 := div_core (q.num * ((2 ^ k : ℕ) : ℤ)) q.den q.den_pos
  rw [Int.cast_mul, cast_pow2] at h2
  have hDr : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.den_pos
  have hk : (2 : ℝ) ^ (-(k : ℤ)) = ((2 : ℝ) ^ k)⁻¹ := by rw [zpow_neg, zpow_natCast]
  have hpk : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  rw [hk, Rat.cast_def, ← div_eq_mul_inv, div_le_iff₀ hpk, div_mul_eq_mul_div, le_div_iff₀ hDr]
  linarith

theorem val_ofRatUp (q : ℚ) : (q : ℝ) ≤ val (Interval128.Dy.ofRatUp q) := by
  unfold Interval128.Dy.ofRatUp
  generalize Interval128.Dy.prec + Interval128.Dy.bitlen q.den = k
  refine le_trans ?_ (val_rup _ _)
  have h2 := div_core (-(q.num * ((2 ^ k : ℕ) : ℤ))) q.den q.den_pos
  rw [Int.cast_neg, Int.cast_mul, cast_pow2] at h2
  have hDr : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.den_pos
  have hk : (2 : ℝ) ^ (-(k : ℤ)) = ((2 : ℝ) ^ k)⁻¹ := by rw [zpow_neg, zpow_natCast]
  have hpk : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  rw [hk, Rat.cast_def, Int.cast_neg, ← div_eq_mul_inv, le_div_iff₀ hpk, div_mul_eq_mul_div,
    div_le_iff₀ hDr]
  linarith

theorem pos_val_eq (a : Dy) (h : 0 < a.m) : val a = ((a.m.toNat : ℕ) : ℝ) * (2 : ℝ) ^ a.e := by
  unfold val; congr 1; exact_mod_cast (Int.toNat_of_nonneg h.le).symm

theorem val_invDnPos (m : ℕ) (e : ℤ) (hm : 0 < m) :
    val (Interval128.Dy.invDnPos m e) ≤ 1 / ((m : ℝ) * (2 : ℝ) ^ e) := by
  unfold Interval128.Dy.invDnPos val
  dsimp only
  set k := Interval128.Dy.prec + Interval128.Dy.bitlen m
  have h1 : (2 ^ k / m) * m ≤ 2 ^ k := Nat.div_mul_le_self _ _
  have h2 : (((2 ^ k / m : ℕ) : ℤ) : ℝ) * (m : ℝ) ≤ (2 : ℝ) ^ k := by
    have : (((2 ^ k / m * m : ℕ)) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at this ⊢; exact this
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have he : (2 : ℝ) ^ (-e - (k : ℤ)) = ((2 : ℝ) ^ e)⁻¹ * ((2 : ℝ) ^ k)⁻¹ := by
    rw [sub_eq_add_neg, zpow_add₀ (by norm_num), zpow_neg, zpow_neg, zpow_natCast]
  have hpk : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hpe := two_zpow_pos e
  rw [he, one_div, mul_inv]
  have : (((2 ^ k / m : ℕ) : ℤ) : ℝ) ≤ (2 : ℝ) ^ k / m := by rw [le_div_iff₀ hmr]; exact h2
  calc (((2 ^ k / m : ℕ) : ℤ) : ℝ) * (((2 : ℝ) ^ e)⁻¹ * ((2 : ℝ) ^ k)⁻¹)
      ≤ (2 : ℝ) ^ k / m * (((2 : ℝ) ^ e)⁻¹ * ((2 : ℝ) ^ k)⁻¹) :=
        mul_le_mul_of_nonneg_right this (by positivity)
    _ = (m : ℝ)⁻¹ * ((2 : ℝ) ^ e)⁻¹ := by field_simp

theorem val_invUpPos (m : ℕ) (e : ℤ) (hm : 0 < m) :
    1 / ((m : ℝ) * (2 : ℝ) ^ e) ≤ val (Interval128.Dy.invUpPos m e) := by
  unfold Interval128.Dy.invUpPos val
  dsimp only
  set k := Interval128.Dy.prec + Interval128.Dy.bitlen m
  have h1 : 2 ^ k ≤ (2 ^ k + m - 1) / m * m := by
    have := Nat.div_add_mod (2 ^ k + m - 1) m
    have := Nat.mod_lt (2 ^ k + m - 1) hm
    rw [Nat.mul_comm]; omega
  have h2 : (2 : ℝ) ^ k ≤ ((((2 ^ k + m - 1) / m : ℕ) : ℤ) : ℝ) * (m : ℝ) := by
    have : ((2 ^ k : ℕ) : ℝ) ≤ ((((2 ^ k + m - 1) / m * m : ℕ)) : ℝ) := by exact_mod_cast h1
    push_cast at this ⊢; exact this
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have he : (2 : ℝ) ^ (-e - (k : ℤ)) = ((2 : ℝ) ^ e)⁻¹ * ((2 : ℝ) ^ k)⁻¹ := by
    rw [sub_eq_add_neg, zpow_add₀ (by norm_num), zpow_neg, zpow_neg, zpow_natCast]
  have hpk : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hpe := two_zpow_pos e
  rw [he, one_div, mul_inv]
  have : (2 : ℝ) ^ k / m ≤ ((((2 ^ k + m - 1) / m : ℕ) : ℤ) : ℝ) := by
    rw [div_le_iff₀ hmr]; exact h2
  calc (m : ℝ)⁻¹ * ((2 : ℝ) ^ e)⁻¹
      = (2 : ℝ) ^ k / m * (((2 : ℝ) ^ e)⁻¹ * ((2 : ℝ) ^ k)⁻¹) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right this (by positivity)

theorem sqrtShift_even (m : ℕ) (e : ℤ) : (e - (Interval128.Dy.sqrtShift m e : ℤ)) % 2 = 0 := by
  unfold Interval128.Dy.sqrtShift
  dsimp only
  split_ifs with h
  · exact h
  · push_cast; omega

/-- `m · 2^e = n · (2^j)^2` with `n = m · 2^k`, `j = (e - k) / 2`. -/
theorem sqrt_split (m : ℕ) (e : ℤ) :
    (m : ℝ) * (2 : ℝ) ^ e = ((m * 2 ^ Interval128.Dy.sqrtShift m e : ℕ) : ℝ) *
      ((2 : ℝ) ^ ((e - (Interval128.Dy.sqrtShift m e : ℤ)) / 2)) ^ 2 := by
  have hev := sqrtShift_even m e
  set k := Interval128.Dy.sqrtShift m e
  have h2 : 2 * ((e - (k : ℤ)) / 2) = e - k := by omega
  push_cast
  rw [← zpow_natCast ((2 : ℝ) ^ ((e - (k : ℤ)) / 2)) 2, ← zpow_mul, mul_comm _ (((2 : ℕ) : ℤ)),
    Nat.cast_ofNat, h2, mul_assoc, ← zpow_natCast (2 : ℝ) k, ← zpow_add₀ (by norm_num)]
  congr 2; ring

theorem sqrt_eq (m : ℕ) (e : ℤ) :
    Real.sqrt ((m : ℝ) * (2 : ℝ) ^ e) = Real.sqrt ((m * 2 ^ Interval128.Dy.sqrtShift m e : ℕ) : ℝ) *
      (2 : ℝ) ^ ((e - (Interval128.Dy.sqrtShift m e : ℤ)) / 2) := by
  rw [sqrt_split, Real.sqrt_mul (by positivity), Real.sqrt_sq (two_zpow_pos _).le]

theorem val_sqrtDn (m : ℕ) (e : ℤ) : val (Interval128.Dy.sqrtDn m e) ≤ Real.sqrt ((m : ℝ) * (2 : ℝ) ^ e) := by
  rw [sqrt_eq]
  unfold Interval128.Dy.sqrtDn val
  dsimp only
  apply mul_le_mul_of_nonneg_right _ (two_zpow_pos _).le
  set n := m * 2 ^ Interval128.Dy.sqrtShift m e
  set r := Interval128.Dy.isqrtG n
  cases hb : Nat.ble (r * r) n
  · simp only [Bool.cond_false, Int.cast_zero]; exact Real.sqrt_nonneg _
  · simp only [Bool.cond_true, Int.cast_natCast]
    have : r * r ≤ n := Nat.le_of_ble_eq_true hb
    apply Real.le_sqrt_of_sq_le
    have : ((r * r : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
    push_cast at this; nlinarith

theorem val_sqrtUp (m : ℕ) (e : ℤ) : Real.sqrt ((m : ℝ) * (2 : ℝ) ^ e) ≤ val (Interval128.Dy.sqrtUp m e) := by
  rw [sqrt_eq]
  unfold Interval128.Dy.sqrtUp val
  dsimp only
  apply mul_le_mul_of_nonneg_right _ (two_zpow_pos _).le
  set n := m * 2 ^ Interval128.Dy.sqrtShift m e
  set r := Interval128.Dy.isqrtG n
  have key : ∀ t : ℕ, n ≤ t * t → Real.sqrt (n : ℝ) ≤ (t : ℝ) := by
    intro t ht
    rw [Real.sqrt_le_left (by positivity)]
    have : ((n : ℕ) : ℝ) ≤ ((t * t : ℕ) : ℝ) := by exact_mod_cast ht
    push_cast at this; nlinarith
  cases hb : Nat.ble n (r * r)
  · simp only [Bool.cond_false]
    cases hb' : Nat.ble n ((r + 1) * (r + 1))
    · simp only [Bool.cond_false, Int.cast_natCast]
      exact key _ (by nlinarith)
    · simp only [Bool.cond_true, Int.cast_natCast]
      exact key _ (Nat.le_of_ble_eq_true hb')
  · simp only [Bool.cond_true, Int.cast_natCast]
    exact key _ (Nat.le_of_ble_eq_true hb)

/-! ### Intervals -/

/-- `x` lies between the finite endpoints of `X`. -/
def mem (x : ℝ) (X : DI) : Prop :=
  (∀ l, X.lo = some l → val l ≤ x) ∧ (∀ h, X.hi = some h → x ≤ val h)

theorem mem_whole (x : ℝ) : mem x DI.whole := ⟨by simp [DI.whole], by simp [DI.whole]⟩

theorem mem_ofRatI {a b : ℚ} {x : ℝ} (h1 : (a : ℝ) ≤ x) (h2 : x ≤ (b : ℝ)) : mem x (DI.ofRatI a b) :=
  ⟨by rintro l ⟨⟩; exact le_trans (val_ofRatDn a) h1,
   by rintro h ⟨⟩; exact le_trans h2 (val_ofRatUp b)⟩

theorem mem_ofRat (q : ℚ) : mem (q : ℝ) (DI.ofRat q) := mem_ofRatI le_rfl le_rfl

theorem mem_neg {X : DI} {x : ℝ} (hx : mem x X) : mem (-x) (DI.neg X) := by
  constructor
  · intro l hl
    simp only [DI.neg, Option.map_eq_some_iff] at hl
    obtain ⟨b, hb, rfl⟩ := hl
    rw [val_neg]; linarith [hx.2 b hb]
  · intro h hh
    simp only [DI.neg, Option.map_eq_some_iff] at hh
    obtain ⟨a, ha, rfl⟩ := hh
    rw [val_neg]; linarith [hx.1 a ha]

theorem mem_add {X Y : DI} {x y : ℝ} (hx : mem x X) (hy : mem y Y) : mem (x + y) (DI.add X Y) := by
  constructor
  · intro l hl
    simp only [DI.add] at hl
    split at hl
    · rename_i a b ha hb
      simp only [Option.some.injEq] at hl; subst hl
      refine le_trans (val_rdn' _) ?_
      rw [val_addX]; linarith [hx.1 a ha, hy.1 b hb]
    · simp at hl
  · intro h hh
    simp only [DI.add] at hh
    split at hh
    · rename_i a b ha hb
      simp only [Option.some.injEq] at hh; subst hh
      refine le_trans ?_ (val_rup' _)
      rw [val_addX]; linarith [hx.2 a ha, hy.2 b hb]
    · simp at hh

theorem mem_sub {X Y : DI} {x y : ℝ} (hx : mem x X) (hy : mem y Y) : mem (x - y) (DI.sub X Y) := by
  rw [sub_eq_add_neg]; exact mem_add hx (mem_neg hy)

/-- Corner bound for a product on a box. -/
theorem mul_corners {a b c d x y : ℝ} (ha : a ≤ x) (hb : x ≤ b) (hc : c ≤ y) (hd : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have hl1 : min (a * y) (b * y) ≤ x * y := by
    rcases le_total 0 y with h | h
    · exact min_le_of_left_le (by nlinarith)
    · exact min_le_of_right_le (by nlinarith)
  have hl2 : min (a * c) (a * d) ≤ a * y := by
    rcases le_total 0 a with h | h
    · exact min_le_of_left_le (by nlinarith)
    · exact min_le_of_right_le (by nlinarith)
  have hl3 : min (b * c) (b * d) ≤ b * y := by
    rcases le_total 0 b with h | h
    · exact min_le_of_left_le (by nlinarith)
    · exact min_le_of_right_le (by nlinarith)
  have hu1 : x * y ≤ max (a * y) (b * y) := by
    rcases le_total 0 y with h | h
    · exact le_max_of_le_right (by nlinarith)
    · exact le_max_of_le_left (by nlinarith)
  have hu2 : a * y ≤ max (a * c) (a * d) := by
    rcases le_total 0 a with h | h
    · exact le_max_of_le_right (by nlinarith)
    · exact le_max_of_le_left (by nlinarith)
  have hu3 : b * y ≤ max (b * c) (b * d) := by
    rcases le_total 0 b with h | h
    · exact le_max_of_le_right (by nlinarith)
    · exact le_max_of_le_left (by nlinarith)
  constructor
  · rcases min_choice (a * y) (b * y) with h | h <;> rw [h] at hl1
    · exact le_trans (min_le_left _ _) (le_trans hl2 hl1)
    · exact le_trans (min_le_right _ _) (le_trans hl3 hl1)
  · rcases max_choice (a * y) (b * y) with h | h <;> rw [h] at hu1
    · exact le_trans hu1 (le_trans hu2 (le_max_left _ _))
    · exact le_trans hu1 (le_trans hu3 (le_max_right _ _))

theorem mem_mul {X Y : DI} {x y : ℝ} (hx : mem x X) (hy : mem y Y) : mem (x * y) (DI.mul X Y) := by
  unfold DI.mul
  split
  · rename_i a b c d ha hb hc hd
    have hxa := hx.1 a ha; have hxb := hx.2 b hb
    have hyc := hy.1 c hc; have hyd := hy.2 d hd
    obtain ⟨h1, h2⟩ := mul_corners hxa hxb hyc hyd
    constructor
    · rintro l ⟨⟩
      refine le_trans (val_rdn' _) (le_trans ?_ h1)
      simp only [le_min_iff]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> rw [← val_mulX]
      · exact le_trans (dmin_le_left _ _) (dmin_le_left _ _)
      · exact le_trans (dmin_le_left _ _) (dmin_le_right _ _)
      · exact le_trans (dmin_le_right _ _) (dmin_le_left _ _)
      · exact le_trans (dmin_le_right _ _) (dmin_le_right _ _)
    · rintro u ⟨⟩
      refine le_trans h2 (le_trans ?_ (val_rup' _))
      simp only [max_le_iff]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> rw [← val_mulX]
      · exact le_trans (dle_max_left _ _) (dle_max_left _ _)
      · exact le_trans (dle_max_right _ _) (dle_max_left _ _)
      · exact le_trans (dle_max_left _ _) (dle_max_right _ _)
      · exact le_trans (dle_max_right _ _) (dle_max_right _ _)
  · exact mem_whole _

theorem mem_inv {X : DI} {x : ℝ} (hx : mem x X) : mem x⁻¹ (DI.inv X) := by
  unfold DI.inv
  split
  · rename_i a b ha hb
    have hxa := hx.1 a ha; have hxb := hx.2 b hb
    split_ifs with h1 h2
    · have hva := (val_pos_iff a).2 h1
      have hx0 : 0 < x := lt_of_lt_of_le hva hxa
      have hbm : 0 < b.m := (val_pos_iff b).1 (by linarith)
      constructor
      · rintro l ⟨⟩
        have := val_invDnPos b.m.toNat b.e (by omega)
        rw [← pos_val_eq b hbm, one_div] at this
        exact le_trans this (inv_anti₀ hx0 hxb)
      · rintro u ⟨⟩
        have := val_invUpPos a.m.toNat a.e (by omega)
        rw [← pos_val_eq a h1, one_div] at this
        exact le_trans (inv_anti₀ hva hxa) this
    · have hvb := (val_neg_iff b).2 h2
      have hx0 : x < 0 := lt_of_le_of_lt hxb hvb
      have ham : a.m < 0 := (val_neg_iff a).1 (by linarith)
      have eb : val b = -(((-b.m).toNat : ℕ) : ℝ) * (2 : ℝ) ^ b.e := by
        unfold val
        have : (((-b.m).toNat : ℕ) : ℤ) = -b.m := Int.toNat_of_nonneg (by omega)
        have : (((-b.m).toNat : ℕ) : ℝ) = -(b.m : ℝ) := by exact_mod_cast this
        rw [this]; ring
      have ea : val a = -(((-a.m).toNat : ℕ) : ℝ) * (2 : ℝ) ^ a.e := by
        unfold val
        have : (((-a.m).toNat : ℕ) : ℤ) = -a.m := Int.toNat_of_nonneg (by omega)
        have : (((-a.m).toNat : ℕ) : ℝ) = -(a.m : ℝ) := by exact_mod_cast this
        rw [this]; ring
      constructor
      · rintro l ⟨⟩
        have := val_invUpPos (-b.m).toNat b.e (by omega)
        rw [val_neg]
        have e1 : 1 / ((((-b.m).toNat : ℕ) : ℝ) * (2 : ℝ) ^ b.e) = -(val b)⁻¹ := by
          rw [eb, one_div, neg_mul, inv_neg, neg_neg]
        rw [e1] at this
        have : (val b)⁻¹ ≤ x⁻¹ := (inv_le_inv_of_neg hvb hx0).2 hxb
        linarith
      · rintro u ⟨⟩
        have := val_invDnPos (-a.m).toNat a.e (by omega)
        rw [val_neg]
        have e1 : 1 / ((((-a.m).toNat : ℕ) : ℝ) * (2 : ℝ) ^ a.e) = -(val a)⁻¹ := by
          rw [ea, one_div, neg_mul, inv_neg, neg_neg]
        rw [e1] at this
        have hva : val a < 0 := by linarith
        have : x⁻¹ ≤ (val a)⁻¹ := (inv_le_inv_of_neg hx0 hva).2 hxa
        linarith
    · exact mem_whole _
  · exact mem_whole _

theorem mem_div {X Y : DI} {x y : ℝ} (hx : mem x X) (hy : mem y Y) : mem (x / y) (DI.div X Y) := by
  rw [div_eq_mul_inv]; exact mem_mul hx (mem_inv hy)

theorem mem_sqrt {X : DI} {x : ℝ} (hx : mem x X) : mem (Real.sqrt x) (DI.sqrt X) := by
  constructor
  · rintro l ⟨⟩
    split
    · rename_i a ha
      split_ifs with h
      · have := val_sqrtDn a.m.toNat a.e
        rw [← pos_val_eq a h] at this
        exact le_trans this (Real.sqrt_le_sqrt (hx.1 a ha))
      · simp only [val, Interval128.Dy.zero]; simp [Real.sqrt_nonneg]
    · simp only [val, Interval128.Dy.zero]; simp [Real.sqrt_nonneg]
  · intro u hu
    simp only [DI.sqrt] at hu
    split at hu
    · rename_i b hb
      simp only [Option.some.injEq] at hu; subst hu
      split_ifs with h
      · have := val_sqrtUp b.m.toNat b.e
        rw [← pos_val_eq b h] at this
        exact le_trans (Real.sqrt_le_sqrt (hx.2 b hb)) this
      · have : val b ≤ 0 := (val_nonpos_iff b).2 (by omega)
        rw [Real.sqrt_eq_zero'.2 (le_trans (hx.2 b hb) this)]
        simp [val, Interval128.Dy.zero]
    · simp at hu

theorem val_zero : val Interval128.Dy.zero = 0 := by simp [val, Interval128.Dy.zero]

theorem mem_abs {X : DI} {x : ℝ} (hx : mem x X) : mem |x| (DI.abs X) := by
  unfold DI.abs
  split
  · rename_i a b ha hb
    have hxa := hx.1 a ha; have hxb := hx.2 b hb
    split_ifs with h1 h2
    · have : 0 ≤ val a := (val_nonneg_iff a).2 h1
      rw [abs_of_nonneg (by linarith)]; exact hx
    · have := (val_nonpos_iff b).2 h2
      rw [abs_of_nonpos (by linarith)]; exact mem_neg hx
    · constructor
      · rintro l ⟨⟩; rw [val_zero]; exact abs_nonneg _
      · rintro u ⟨⟩
        rcases le_total 0 x with h | h
        · rw [abs_of_nonneg h]; exact le_trans hxb (dle_max_right _ _)
        · rw [abs_of_nonpos h]; refine le_trans ?_ (dle_max_left _ _); rw [val_neg]; linarith
  · rename_i a ha hb
    have hxa := hx.1 a ha
    split_ifs with h1
    · have : 0 ≤ val a := (val_nonneg_iff a).2 h1
      rw [abs_of_nonneg (by linarith)]; exact hx
    · exact ⟨by rintro l ⟨⟩; rw [val_zero]; exact abs_nonneg _, by simp⟩
  · rename_i b ha hb
    have hxb := hx.2 b hb
    split_ifs with h2
    · have := (val_nonpos_iff b).2 h2
      rw [abs_of_nonpos (by linarith)]; exact mem_neg hx
    · exact ⟨by rintro l ⟨⟩; rw [val_zero]; exact abs_nonneg _, by simp⟩
  · exact ⟨by rintro l ⟨⟩; rw [val_zero]; exact abs_nonneg _, by simp⟩

theorem mem_mulPow {X : DI} {x : ℝ} (hx : mem x X) (n : ℕ) : mem (x ^ n) (DI.mulPow X n) := by
  induction n with
  | zero => rw [pow_zero]; have := mem_ofRat 1; rw [Rat.cast_one] at this; exact this
  | succ n ih => rw [pow_succ]; exact mem_mul ih hx

theorem mem_pow {X : DI} {x : ℝ} (hx : mem x X) (n : ℕ) : mem (x ^ n) (DI.pow X n) := by
  unfold DI.pow
  split_ifs with c
  · have he : Even n := Nat.even_iff.2 c
    rw [← he.pow_abs]; exact mem_mulPow (mem_abs hx) n
  · exact mem_mulPow hx n

theorem mem_pi : mem Real.pi DI.pi := by
  apply mem_ofRatI
  · have := RealFP.pi_gt_d40; simp only [Interval128.Dy.piLo]; push_cast; linarith
  · have := RealFP.pi_lt_d40; simp only [Interval128.Dy.piHi]; push_cast; linarith

/-! ### Lifts through Interval64 -/

theorem decLo_le {R : KI} (hw : WF R) {y : ℝ} (hy : y ∈ (toI R).toSet) :
    ∀ l, Interval128.Dy.decLo R.lo = some l → val l ≤ y := by
  intro l hl
  unfold Interval128.Dy.decLo at hl
  split_ifs at hl with hn
  simp only [Option.map_eq_some_iff] at hl
  obtain ⟨q, hq, rfl⟩ := hl
  have hb : (toF R.lo).toBits = UInt64.ofNat R.lo :=
    toBits_toF_of_not_nan hw.1 (by simpa using hn)
  rw [← hb] at hq
  have hfv := toReal?_of_bitsToRat? hq
  have h1 := ((mem_toSet_iff_toE).1 hy).1.2
  rw [lo_toI', RealFP.I128.toE_of_fv hfv] at h1
  exact le_trans (val_ofRatDn q) (EReal.coe_le_coe_iff.1 h1)

theorem decHi_ge {R : KI} (hw : WF R) {y : ℝ} (hy : y ∈ (toI R).toSet) :
    ∀ u, Interval128.Dy.decHi R.hi = some u → y ≤ val u := by
  intro u hu
  unfold Interval128.Dy.decHi at hu
  split_ifs at hu with hn
  simp only [Option.map_eq_some_iff] at hu
  obtain ⟨q, hq, rfl⟩ := hu
  have hb : (toF R.hi).toBits = UInt64.ofNat R.hi :=
    toBits_toF_of_not_nan hw.2 (by simpa using hn)
  rw [← hb] at hq
  have hfv := toReal?_of_bitsToRat? hq
  have h1 := ((mem_toSet_iff_toE).1 hy).2.2
  rw [hi_toI', RealFP.I128.toE_of_fv hfv] at h1
  exact le_trans (EReal.coe_le_coe_iff.1 h1) (val_ofRatUp q)

theorem ofRat_mem {a b : Dy} {x : ℝ} (ha : val a ≤ x) (hb : x ≤ val b) :
    x ∈ (toI (KI.ofRatInterval (Interval128.Dy.toRat a) (Interval128.Dy.toRat b))).toSet ∧
      WF (KI.ofRatInterval (Interval128.Dy.toRat a) (Interval128.Dy.toRat b)) := by
  obtain ⟨h1, h2⟩ := ofRatInterval_toI (Interval128.Dy.toRat a) (Interval128.Dy.toRat b)
  refine ⟨?_, h2⟩
  rw [h1]
  exact mem_toSet_ofRatInterval (by rw [toRat_val]; exact ha) (by rw [toRat_val]; exact hb)

set_option linter.concreteInstances false
variable [ExtTbl] [ExtSem]

theorem mem_lift1 (f : IExpr) {X : DI} {x : ℝ} (hx : mem x X) : mem (f.denote [x]) (Interval128.Dy.lift1 f X) := by
  unfold Interval128.Dy.lift1
  split
  · rename_i a b ha hb
    obtain ⟨hm, hw⟩ := ofRat_mem (hx.1 a ha) (hx.2 b hb)
    have hwf : ∀ Y ∈ [KI.ofRatInterval (Interval128.Dy.toRat a) (Interval128.Dy.toRat b)], WF Y := by simpa using hw
    have hs := eval_sound (List.Forall₂.cons hm List.Forall₂.nil) f
    have h1 := (evalK_toI hwf f).1
    simp only [List.map_cons, List.map_nil] at h1
    rw [← h1] at hs
    have hwR := (evalK_toI hwf f).2
    exact ⟨decLo_le hwR hs, decHi_ge hwR hs⟩
  · exact mem_whole _

theorem mem_lift2 (f : IExpr) {X Y : DI} {x y : ℝ} (hx : mem x X) (hy : mem y Y) :
    mem (f.denote [x, y]) (Interval128.Dy.lift2 f X Y) := by
  unfold Interval128.Dy.lift2
  split
  · rename_i a b c d ha hb hc hd
    obtain ⟨hm, hw⟩ := ofRat_mem (hx.1 a ha) (hx.2 b hb)
    obtain ⟨hm', hw'⟩ := ofRat_mem (hy.1 c hc) (hy.2 d hd)
    have hwf : ∀ Z ∈ [KI.ofRatInterval (Interval128.Dy.toRat a) (Interval128.Dy.toRat b), KI.ofRatInterval (Interval128.Dy.toRat c) (Interval128.Dy.toRat d)],
        WF Z := by simp [hw, hw']
    have hs := eval_sound (List.Forall₂.cons hm (List.Forall₂.cons hm' List.Forall₂.nil)) f
    have h1 := (evalK_toI hwf f).1
    simp only [List.map_cons, List.map_nil] at h1
    rw [← h1] at hs
    have hwR := (evalK_toI hwf f).2
    exact ⟨decLo_le hwR hs, decHi_ge hwR hs⟩
  · exact mem_whole _

/-! ### Evaluation -/

omit [ExtTbl] [ExtSem] in
theorem getD_mem {xs : List ℝ} {env : List DI} (h : List.Forall₂ mem xs env) (i : ℕ) :
    mem (xs.getD i 0) (env.getD i DI.zero) := by
  induction h generalizing i with
  | nil =>
    simp only [List.getD_nil]
    exact ⟨by rintro l ⟨⟩; rw [val_zero], by rintro l ⟨⟩; rw [val_zero]⟩
  | cons hxX _ ih =>
    cases i with
    | zero => simpa using hxX
    | succ n => simpa using ih n

theorem evalQ_sound {xs : List ℝ} {env : List DI} (h : List.Forall₂ mem xs env) :
    ∀ e : IExpr, mem (e.denote xs) (Interval128.Dy.evalQ env e) := by
  intro e
  induction e with
  | var i => exact getD_mem h i
  | rat q => exact mem_ofRat q
  | add a b iha ihb => exact mem_add iha ihb
  | sub a b iha ihb => exact mem_sub iha ihb
  | mul a b iha ihb => exact mem_mul iha ihb
  | div a b iha ihb => exact mem_div iha ihb
  | neg a iha => exact mem_neg iha
  | inv a iha => exact mem_inv iha
  | sqrt a iha => exact mem_sqrt iha
  | abs a iha => exact mem_abs iha
  | pow a n iha => exact mem_pow iha n
  | exp a iha => exact mem_lift1 (.exp (.var 0)) iha
  | log a iha => exact mem_lift1 (.log (.var 0)) iha
  | sin a iha => exact mem_lift1 (.sin (.var 0)) iha
  | cos a iha => exact mem_lift1 (.cos (.var 0)) iha
  | pi => exact mem_pi
  | atan a iha => exact mem_lift1 (.atan (.var 0)) iha
  | atan2 a b iha ihb => exact mem_lift2 (.atan2 (.var 0) (.var 1)) iha ihb
  | sinh a iha => exact mem_lift1 (.sinh (.var 0)) iha
  | cosh a iha => exact mem_lift1 (.cosh (.var 0)) iha
  | tanh a iha => exact mem_lift1 (.tanh (.var 0)) iha
  | log2 a iha => exact mem_lift1 (.log2 (.var 0)) iha
  | log10 a iha => exact mem_lift1 (.log10 (.var 0)) iha
  | tan a iha => exact mem_lift1 (.tan (.var 0)) iha
  | asin a iha => exact mem_lift1 (.asin (.var 0)) iha
  | acos a iha => exact mem_lift1 (.acos (.var 0)) iha
  | ext k d a _ iha => exact mem_lift1 (.ext k d (.var 0)) iha

/-! ### Bisection -/

omit [ExtTbl] [ExtSem] in
theorem split_mem {X : DI} {y : ℝ} (d : Dy) (hy : mem y X) :
    mem y (Interval128.Dy.leftAt X d) ∨ mem y (Interval128.Dy.rightAt X d) := by
  rcases le_total y (val d) with h | h
  · exact Or.inl ⟨hy.1, by rintro u ⟨⟩; exact h⟩
  · exact Or.inr ⟨by rintro l ⟨⟩; exact h, hy.2⟩

omit [ExtTbl] [ExtSem] in
theorem forall2_set {xs : List ℝ} {env : List DI} (h : List.Forall₂ mem xs env) (i : ℕ) {Y : DI}
    (hY : mem (xs.getD i 0) Y) : List.Forall₂ mem xs (env.set i Y) := by
  induction h generalizing i with
  | nil => simp
  | cons hxX _ ih =>
    cases i with
    | zero => exact List.Forall₂.cons (by simpa using hY) (by assumption)
    | succ n => exact List.Forall₂.cons hxX (ih n (by simpa using hY))

theorem checkQ_sound (e : IExpr) (g : DI → Bool) (P : ℝ → Prop)
    (hg : ∀ F, g F = true → ∀ y, mem y F → P y) :
    ∀ (c : Interval128.Dy.Cert) (env : List DI) (xs : List ℝ),
      List.Forall₂ mem xs env → Interval128.Dy.checkQ e g c env = true → P (e.denote xs) := by
  intro c
  induction c with
  | leaf =>
    intro env xs hxs hc
    exact hg _ hc _ (evalQ_sound hxs e)
  | split i q l r ihl ihr =>
    intro env xs hxs hc
    simp only [Interval128.Dy.checkQ, Bool.and_eq_true] at hc
    rcases split_mem q (getD_mem hxs i) with h1 | h1
    · exact ihl _ xs (forall2_set hxs i h1) hc.1
    · exact ihr _ xs (forall2_set hxs i h1) hc.2

omit [ExtSem] in
theorem checkQ_split_of (e : IExpr) (g : DI → Bool) (i : ℕ) (q : Dy)
    (l r : Interval128.Dy.Cert) (env : List DI)
    (hl : Interval128.Dy.checkQ e g l (env.set i (Interval128.Dy.leftAt (env.getD i DI.zero) q)) = true)
    (hr : Interval128.Dy.checkQ e g r (env.set i (Interval128.Dy.rightAt (env.getD i DI.zero) q)) = true) :
    Interval128.Dy.checkQ e g (.split i q l r) env = true := by
  simp only [Interval128.Dy.checkQ, hl, hr, Bool.and_self]

/-! ### Goal predicates -/

omit [ExtTbl] [ExtSem] in
theorem gLe_sound (c : ℚ) : ∀ F, Interval128.Dy.gLe c F = true → ∀ y, mem y F → y ≤ (c : ℝ) := by
  intro F hg y hy
  unfold Interval128.Dy.gLe at hg
  split at hg
  · rename_i u hu
    have h2 : ((Interval128.Dy.toRat u : ℚ) : ℝ) ≤ c := by exact_mod_cast of_decide_eq_true hg
    rw [toRat_val] at h2; linarith [hy.2 u hu]
  · simp at hg

omit [ExtTbl] [ExtSem] in
theorem gLt_sound (c : ℚ) : ∀ F, Interval128.Dy.gLt c F = true → ∀ y, mem y F → y < (c : ℝ) := by
  intro F hg y hy
  unfold Interval128.Dy.gLt at hg
  split at hg
  · rename_i u hu
    have h2 : ((Interval128.Dy.toRat u : ℚ) : ℝ) < c := by exact_mod_cast of_decide_eq_true hg
    rw [toRat_val] at h2; linarith [hy.2 u hu]
  · simp at hg

omit [ExtTbl] [ExtSem] in
theorem gGe_sound (c : ℚ) : ∀ F, Interval128.Dy.gGe c F = true → ∀ y, mem y F → (c : ℝ) ≤ y := by
  intro F hg y hy
  unfold Interval128.Dy.gGe at hg
  split at hg
  · rename_i u hu
    have h2 : (c : ℝ) ≤ ((Interval128.Dy.toRat u : ℚ) : ℝ) := by exact_mod_cast of_decide_eq_true hg
    rw [toRat_val] at h2; linarith [hy.1 u hu]
  · simp at hg

omit [ExtTbl] [ExtSem] in
theorem gGt_sound (c : ℚ) : ∀ F, Interval128.Dy.gGt c F = true → ∀ y, mem y F → (c : ℝ) < y := by
  intro F hg y hy
  unfold Interval128.Dy.gGt at hg
  split at hg
  · rename_i u hu
    have h2 : (c : ℝ) < ((Interval128.Dy.toRat u : ℚ) : ℝ) := by exact_mod_cast of_decide_eq_true hg
    rw [toRat_val] at h2; linarith [hy.1 u hu]
  · simp at hg

/-! ### Entry points for the tactic -/

omit [ExtTbl] [ExtSem] in
theorem boxes_mem {xs : List ℝ} {bs : List (ℚ × ℚ)} (h : InBoxes xs bs) :
    List.Forall₂ mem xs (Interval128.Dy.boxes bs) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hx _ ih => exact List.Forall₂.cons (mem_ofRatI hx.1 hx.2) ih

theorem prove_le (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : Interval128.Dy.Cert)
    (h : Interval128.Dy.checkQ e (Interval128.Dy.gLe c) cert (Interval128.Dy.boxes bs) = true) (xs : List ℝ)
    (hxs : InBoxes xs bs) : e.denote xs ≤ (c : ℝ) :=
  checkQ_sound e _ _ (gLe_sound c) cert _ xs (boxes_mem hxs) h

theorem prove_lt (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : Interval128.Dy.Cert)
    (h : Interval128.Dy.checkQ e (Interval128.Dy.gLt c) cert (Interval128.Dy.boxes bs) = true) (xs : List ℝ)
    (hxs : InBoxes xs bs) : e.denote xs < (c : ℝ) :=
  checkQ_sound e _ _ (gLt_sound c) cert _ xs (boxes_mem hxs) h

theorem prove_ge (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : Interval128.Dy.Cert)
    (h : Interval128.Dy.checkQ e (Interval128.Dy.gGe c) cert (Interval128.Dy.boxes bs) = true) (xs : List ℝ)
    (hxs : InBoxes xs bs) : (c : ℝ) ≤ e.denote xs :=
  checkQ_sound e _ _ (gGe_sound c) cert _ xs (boxes_mem hxs) h

theorem prove_gt (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : Interval128.Dy.Cert)
    (h : Interval128.Dy.checkQ e (Interval128.Dy.gGt c) cert (Interval128.Dy.boxes bs) = true) (xs : List ℝ)
    (hxs : InBoxes xs bs) : (c : ℝ) < e.denote xs :=
  checkQ_sound e _ _ (gGt_sound c) cert _ xs (boxes_mem hxs) h

end RealFP.I128Q
