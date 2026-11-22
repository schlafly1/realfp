/-
Soundness of the interval positive-definiteness certificate (`Interval64.Mat`, core file
`Interval64/Matrix.lean`).

* `IMat.Mem M A` : the real matrix `A` lies in the interval matrix `M` (entrywise).
* `posDef_of_pdCheck` : `pdCheck M X = true` → every symmetric `A ∈ M` is positive definite.
* `posDef_of_isPD` : the same for `isPD M` (default congruence).
* `posDef_sub_of_lamMinCheck` / `lt_quad_of_lamMinCheck` / `lt_eigenvalue_of_lamMinCheck` :
  `λ_min(A) > s`.
* `posDef_sub_of_gtCheck` : `A - B` positive definite for all symmetric `A ∈ M`, `B ∈ N`.
-/
import RealFPMathlib.MatrixPD
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import RealFPMathlib.Conv
import RealFPMathlib.Ops
import Interval64.Matrix

open Interval64 Interval64.Mat Matrix Finset

noncomputable section

namespace RealFP.Mat

/-! ### Interval lemmas -/

theorem zeroI_mem : (0 : ℝ) ∈ Interval64.Mat.zeroI :=
  mem_point (f := 0) isNaN_zero (by simp)

/-- A finite float's real value lies in its point interval. -/
theorem toReal_mem_point {f : Float} (hn : f.isNaN = false) (hi : f.isInf = false) :
    f.toReal ∈ point f := by
  have hb : f.toE ≠ ⊥ := fun h => by
    have := (isInf_iff_toE (f := f)).2 ⟨Or.inr h, hn⟩; rw [hi] at this; exact absurd this (by simp)
  have ht : f.toE ≠ ⊤ := fun h => by
    have := (isInf_iff_toE (f := f)).2 ⟨Or.inl h, hn⟩; rw [hi] at this; exact absurd this (by simp)
  obtain ⟨q, hq, he⟩ := exists_rat_of_toE hn hb ht
  rw [toReal_of_bitsToRat? hq]
  exact mem_point hn he

theorem mem_idot {f g : ℕ → Interval64} {u v : ℕ → ℝ} :
    ∀ len, (∀ k < len, u k ∈ f k) → (∀ k < len, v k ∈ g k) →
      (∑ k ∈ range len, u k * v k) ∈ idot f g len
  | 0, _, _ => by simpa [idot] using zeroI_mem
  | len + 1, hu, hv => by
    rw [sum_range_succ]
    exact Iv.add_mem (mem_idot len (fun k hk => hu k (by omega)) (fun k hk => hv k (by omega)))
      (Iv.mem_mul (hu len (by omega)) (hv len (by omega)))

theorem mem_isumSkip {f : ℕ → Interval64} {u : ℕ → ℝ} (skip : ℕ) :
    ∀ len, (∀ k < len, k ≠ skip → u k ∈ f k) →
      (∑ k ∈ range len, if k = skip then 0 else u k) ∈ isumSkip f skip len
  | 0, _ => by simpa [isumSkip] using zeroI_mem
  | len + 1, hu => by
    rw [sum_range_succ]
    have ih := mem_isumSkip skip len (fun k hk hks => hu k (by omega) hks)
    by_cases h : len = skip
    · simpa [isumSkip, h] using ih
    · simp only [isumSkip, h, ite_false]
      exact Iv.add_mem ih (hu len (by omega) h)

theorem pos_of_mem_lo {R : Interval64} {x : ℝ} (hx : x ∈ R) (h : (0 : Float) < R.lo) : 0 < x := by
  obtain ⟨⟨hl, hl'⟩, -⟩ := mem_toSet_iff_toE.1 hx
  have : (0 : EReal) < R.lo.toE := (zero_lt_iff_toE hl).1 h
  exact EReal.coe_pos.1 (lt_of_lt_of_le this hl')

/-! ### Array / index plumbing -/

theorem fget_ofFn {m : ℕ} {f : ℕ → Float} {k : ℕ} (hk : k < m) :
    fget (Interval64.FloatArray.ofFn m f) k = f k := by
  have hs : k < (Interval64.FloatArray.ofFn m f).size := by
    simp [Interval64.FloatArray.ofFn, FloatArray.size, hk]
  simp only [fget, hs, ↓reduceDIte]
  show (Interval64.FloatArray.ofFn m f).data[k] = f k
  simp [Interval64.FloatArray.ofFn]

theorem getD_ofFn {m : ℕ} {f : Fin m → Interval64} {k : ℕ} (hk : k < m) (d : Interval64) :
    (Array.ofFn f).getD k d = f ⟨k, hk⟩ := by
  simp [Array.getD, hk]

theorem idx_div {n i k : ℕ} (hk : k < n) : (i * n + k) / n = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hk, Nat.zero_add]

theorem idx_mod {n i k : ℕ} (hk : k < n) : (i * n + k) % n = k := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]

theorem idx_lt {n i k : ℕ} (hi : i < n) (hk : k < n) : i * n + k < n * n := by
  nlinarith


/-! ### Real side -/

/-- The real matrix `A` lies entrywise in the interval matrix `M`. -/
def _root_.Interval64.IMat.Mem (M : IMat) (A : Matrix (Fin M.n) (Fin M.n) ℝ) : Prop :=
  ∀ i j : Fin M.n, A i j ∈ M.get i j

/-- Zero extension of a matrix to `ℕ × ℕ`. -/
def ext {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (i j : ℕ) : ℝ :=
  if h : i < n ∧ j < n then C ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

theorem ext_fin {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : ext C i j = C i j := by
  simp [ext]

/-- Real value of `X[i, j]`. -/
def xr (n : ℕ) (X : FloatArray) (i j : ℕ) : ℝ := (fget X (i * n + j)).toReal

/-- The lower-triangular real matrix of `X`. -/
def xm (n : ℕ) (X : FloatArray) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if (j : ℕ) ≤ i then xr n X i j else 0

theorem sum_fin_tri {n i : ℕ} (hi : i < n) (F : Fin n → ℝ) :
    (∑ j : Fin n, if (j : ℕ) ≤ i then F j else 0) =
      ∑ j ∈ range (i + 1), if h : j < n then F ⟨j, h⟩ else 0 := by
  set G : ℕ → ℝ := fun j => if h : j < n then (if j ≤ i then F ⟨j, h⟩ else 0) else 0 with hG
  calc (∑ j : Fin n, if (j : ℕ) ≤ i then F j else 0) = ∑ j : Fin n, G j :=
        Finset.sum_congr rfl fun j _ => by simp [hG, j.isLt]
    _ = ∑ j ∈ range n, G j := Fin.sum_univ_eq_sum_range G n
    _ = (∑ j ∈ range (i + 1), G j) + ∑ j ∈ Ico (i + 1) n, G j :=
        (Finset.sum_range_add_sum_Ico G (by omega)).symm
    _ = _ := by
        rw [Finset.sum_eq_zero (s := Ico (i + 1) n) (fun j hj => by
          simp only [Finset.mem_Ico] at hj
          simp only [hG]; split_ifs with h1 h2 <;> first | rfl | omega), add_zero]
        refine Finset.sum_congr rfl fun j hj => ?_
        simp only [Finset.mem_range] at hj
        simp only [hG]; split_ifs with h1 h2 <;> first | rfl | omega


theorem xmA_apply {n : ℕ} (X : FloatArray) (A : Matrix (Fin n) (Fin n) ℝ) (i k : Fin n) :
    (xm n X * A) i k = ∑ j ∈ range (i + 1), xr n X i j * ext A j k := by
  rw [Matrix.mul_apply]
  simp only [xm, ite_mul, zero_mul]
  rw [sum_fin_tri i.isLt (fun j => xr n X i j * A j k)]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range] at hj
  have hjn : j < n := by omega
  simp [hjn, ext]

theorem mulXmT_apply {n : ℕ} (X : FloatArray) (C : Matrix (Fin n) (Fin n) ℝ) (i l : Fin n) :
    (C * (xm n X)ᵀ) i l = ∑ k ∈ range (l + 1), ext C i k * xr n X l k := by
  rw [Matrix.mul_apply]
  simp only [transpose_apply, xm, mul_ite, mul_zero]
  rw [sum_fin_tri l.isLt (fun k => C i k * xr n X l k)]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  have hkn : k < n := by omega
  simp [hkn, ext]

/-- The used entries of `X` are finite. -/
def XFin (n : ℕ) (X : FloatArray) : Prop :=
  ∀ i j, i < n → j ≤ i → (fget X (i * n + j)).isNaN = false ∧ (fget X (i * n + j)).isInf = false

theorem xFin_of_xFinite {n : ℕ} {X : FloatArray} (h : xFinite n X = true) : XFin n X := by
  intro i j hi hj
  simp only [xFinite, List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h i hi j (by omega)

theorem xr_mem {n : ℕ} {X : FloatArray} (hX : XFin n X) {i j : ℕ} (hi : i < n) (hj : j ≤ i) :
    xr n X i j ∈ xent n X i j :=
  toReal_mem_point (hX i j hi hj).1 (hX i j hi hj).2

section
variable {M : IMat} {X : FloatArray} {A : Matrix (Fin M.n) (Fin M.n) ℝ}

theorem tEntry_mem (hM : M.Mem A) (hX : XFin M.n X) (i k : Fin M.n) :
    (xm M.n X * A) i k ∈ tEntry M X i k := by
  rw [xmA_apply]
  refine mem_idot (i + 1) (fun j hj => xr_mem hX i.isLt (by omega)) (fun j hj => ?_)
  have hjn : j < M.n := by omega
  have : ext A j k = A ⟨j, hjn⟩ k := by simp [ext, hjn]
  rw [this]; exact hM ⟨j, hjn⟩ k

theorem tArr_getD (i k : Fin M.n) : (tArr M X).getD (i * M.n + k) zeroI = tEntry M X i k := by
  rw [tArr, getD_ofFn (idx_lt i.isLt k.isLt)]
  simp only [idx_div k.isLt, idx_mod k.isLt]

theorem bArr_getD {i l : Fin M.n} (hli : (l : ℕ) ≤ i) :
    (bArr M X).getD (i * M.n + l) zeroI = bEntry M X (tArr M X) i l := by
  rw [bArr]
  rw [getD_ofFn (idx_lt i.isLt l.isLt)]
  simp only [idx_div l.isLt, idx_mod l.isLt, hli, ↓reduceIte]

/-- `B = X A Xᵀ`. -/
def bm (n : ℕ) (X : FloatArray) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  xm n X * A * (xm n X)ᵀ

theorem bm_symm {n : ℕ} {X : FloatArray} {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A) :
    (bm n X A)ᵀ = bm n X A := by
  simp [bm, transpose_mul, hA, Matrix.mul_assoc]

theorem bEntry_mem (hM : M.Mem A) (hX : XFin M.n X) (i l : Fin M.n) :
    bm M.n X A i l ∈ bEntry M X (tArr M X) i l := by
  rw [bm, mulXmT_apply]
  refine mem_idot (l + 1) (fun k hk => ?_) (fun k hk => xr_mem hX l.isLt (by omega))
  have hkn : k < M.n := by omega
  have e : ext (xm M.n X * A) i k = (xm M.n X * A) i ⟨k, hkn⟩ := by simp [ext, hkn]
  rw [e, show i * M.n + k = i * M.n + (⟨k, hkn⟩ : Fin M.n) from rfl, tArr_getD]
  exact tEntry_mem hM hX i ⟨k, hkn⟩

theorem bget_mem (hA : Aᵀ = A) (hM : M.Mem A) (hX : XFin M.n X) (i l : Fin M.n) :
    bm M.n X A i l ∈ bget M.n (bArr M X) i l := by
  unfold bget
  by_cases hli : (l : ℕ) ≤ i
  · simp only [hli, ↓reduceIte]; rw [bArr_getD hli]; exact bEntry_mem hM hX i l
  · simp only [hli, ↓reduceIte]; rw [bArr_getD (by omega)]
    have := bEntry_mem hM hX (A := A) l i
    have hs := congrFun (congrFun (bm_symm (X := X) hA) i) l
    rw [transpose_apply] at hs
    rwa [← hs]

theorem offSum_eq (B : Matrix (Fin M.n) (Fin M.n) ℝ) (i : Fin M.n) :
    offSum B i = ∑ l ∈ range M.n, if l = (i : ℕ) then 0 else |ext B i l| := by
  rw [offSum, ← Fin.sum_univ_eq_sum_range (fun l => if l = (i : ℕ) then 0 else |ext B i l|)]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [Fin.val_inj, ext_fin]

theorem margin_mem (hA : Aᵀ = A) (hM : M.Mem A) (hX : XFin M.n X) (i : Fin M.n) :
    bm M.n X A i i - offSum (bm M.n X A) i ∈ margin M.n (bArr M X) i := by
  unfold margin
  refine Iv.sub_mem (bget_mem hA hM hX i i) ?_
  rw [offSum_eq]
  refine mem_isumSkip (i : ℕ) M.n (fun l hl _ => ?_)
  have : ext (bm M.n X A) i l = bm M.n X A i ⟨l, hl⟩ := by simp [ext, hl]
  rw [this]
  exact mem_abs (bget_mem hA hM hX i ⟨l, hl⟩)

theorem fget_pdMargins (i : Fin M.n) :
    fget (pdMargins M X) (2 * i) = (margin M.n (bArr M X) i).lo := by
  show fget (pdMarginsSpec M X) (2 * i) = _
  rw [pdMarginsSpec]
  simp only
  rw [fget_ofFn (by omega)]
  simp

end

/-- **Soundness of the positive-definiteness certificate.** If `pdCheck M X = true`, every
    real symmetric matrix in the interval matrix `M` is positive definite. -/
theorem posDef_of_pdCheck {M : IMat} {X : FloatArray} (h : pdCheck M X = true)
    {A : Matrix (Fin M.n) (Fin M.n) ℝ} (hA : Aᵀ = A) (hM : M.Mem A) : A.PosDef := by
  simp only [pdCheck, Bool.and_eq_true] at h
  obtain ⟨hx, hm⟩ := h
  have hX := xFin_of_xFinite hx
  simp only [marginsPos, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hm
  have hB : (bm M.n X A).PosDef := by
    refine posDef_of_diagDom (bm_symm hA) fun i => ?_
    have h1 := margin_mem hA hM hX i
    have h2 := hm i i.isLt
    rw [fget_pdMargins] at h2
    exact sub_pos.1 (pos_of_mem_lo h1 h2)
  exact posDef_of_posDef_congr hB

/-- `isPD M = true` → every real symmetric `A ∈ M` is positive definite. -/
theorem posDef_of_isPD {M : IMat} (h : isPD M = true)
    {A : Matrix (Fin M.n) (Fin M.n) ℝ} (hA : Aᵀ = A) (hM : M.Mem A) : A.PosDef :=
  posDef_of_pdCheck h hA hM

/-! ### `λ_min` and Loewner comparisons -/

theorem get_ofFn {n : ℕ} {f : ℕ → ℕ → Interval64} {i j : ℕ} (hi : i < n) (hj : j < n) :
    (IMat.ofFn n f).get i j = f i j := by
  simp only [IMat.get, IMat.ofFn]
  rw [fget_ofFn (idx_lt hi hj), fget_ofFn (idx_lt hi hj)]
  simp only [idx_div hj, idx_mod hj]

theorem mem_subDiag {M : IMat} {s : Float} (hn : s.isNaN = false) (hi : s.isInf = false)
    {A : Matrix (Fin M.n) (Fin M.n) ℝ} (hM : M.Mem A) :
    (M.subDiag s).Mem (A - s.toReal • (1 : Matrix (Fin M.n) (Fin M.n) ℝ)) := by
  intro i j
  obtain ⟨i, hi'⟩ := i
  obtain ⟨j, hj'⟩ := j
  change i < M.n at hi'
  change j < M.n at hj'
  show _ ∈ (IMat.ofFn M.n _).get i j
  rw [get_ofFn hi' hj']
  change (A - s.toReal • (1 : Matrix (Fin M.n) (Fin M.n) ℝ)) ⟨i, hi'⟩ ⟨j, hj'⟩ ∈ _
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one]
    exact Iv.sub_mem (hM ⟨i, hi'⟩ ⟨i, hi'⟩) (toReal_mem_point hn hi)
  · have hv : (⟨i, hi'⟩ : Fin M.n) ≠ ⟨j, hj'⟩ := fun h => hij (Fin.mk.inj h)
    simp only [hij, ↓reduceIte, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply_ne hv, smul_eq_mul, mul_zero, sub_zero]
    exact hM ⟨i, hi'⟩ ⟨j, hj'⟩

/-- `lamMinCheck M X s = true` → `A - s I` is positive definite for every symmetric `A ∈ M`. -/
theorem posDef_sub_of_lamMinCheck {M : IMat} {X : FloatArray} {s : Float}
    (h : lamMinCheck M X s = true) {A : Matrix (Fin M.n) (Fin M.n) ℝ} (hA : Aᵀ = A)
    (hM : M.Mem A) : (A - s.toReal • (1 : Matrix (Fin M.n) (Fin M.n) ℝ)).PosDef := by
  simp only [lamMinCheck, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hn, hi⟩, hc⟩ := h
  refine posDef_of_pdCheck (M := M.subDiag s) hc ?_ (mem_subDiag hn hi hM)
  show (A - s.toReal • (1 : Matrix (Fin M.n) (Fin M.n) ℝ))ᵀ = _
  rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hA]

/-- `λ_min(A) > s` as a quadratic-form bound. -/
theorem lt_quad_of_lamMinCheck {M : IMat} {X : FloatArray} {s : Float}
    (h : lamMinCheck M X s = true) {A : Matrix (Fin M.n) (Fin M.n) ℝ} (hA : Aᵀ = A)
    (hM : M.Mem A) {x : Fin M.n → ℝ} (hx : x ≠ 0) :
    s.toReal * (x ⬝ᵥ x) < x ⬝ᵥ (A *ᵥ x) := by
  have := (posDef_iff_dotProduct_mulVec.1 (posDef_sub_of_lamMinCheck h hA hM)).2 hx
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at this
  linarith

/-- Every eigenvalue of `A` exceeds `s`. -/
theorem lt_eigenvalue_of_lamMinCheck {M : IMat} {X : FloatArray} {s : Float}
    (h : lamMinCheck M X s = true) {A : Matrix (Fin M.n) (Fin M.n) ℝ} (hA : Aᵀ = A)
    (hM : M.Mem A) {μ : ℝ} (hμ : Module.End.HasEigenvalue (Matrix.toLin' A) μ) :
    s.toReal < μ := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hAv : A *ᵥ v = μ • v := by
    have := Module.End.mem_eigenspace_iff.1 hv.1
    rwa [Matrix.toLin'_apply] at this
  have hlt := lt_quad_of_lamMinCheck h hA hM hv.2
  rw [hAv, dotProduct_smul, smul_eq_mul] at hlt
  have hd : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  by_contra hc
  push Not at hc
  nlinarith

theorem mem_sub_imat {M N : IMat} {A B : Matrix (Fin M.n) (Fin M.n) ℝ} (hM : M.Mem A)
    (hN : ∀ i j : Fin M.n, B i j ∈ N.get i j) : (M.sub N).Mem (A - B) := by
  intro i j
  obtain ⟨i, hi'⟩ := i
  obtain ⟨j, hj'⟩ := j
  change i < M.n at hi'
  change j < M.n at hj'
  show _ ∈ (IMat.ofFn M.n _).get i j
  rw [get_ofFn hi' hj']
  exact Iv.sub_mem (hM ⟨i, hi'⟩ ⟨j, hj'⟩) (hN ⟨i, hi'⟩ ⟨j, hj'⟩)

/-- `gtCheck M N X = true` → `A - B` is positive definite (`A > B` in the Loewner order) for
    all symmetric `A ∈ M`, `B ∈ N`. -/
theorem posDef_sub_of_gtCheck {M N : IMat} {X : FloatArray} (h : gtCheck M N X = true)
    {A B : Matrix (Fin M.n) (Fin M.n) ℝ} (hA : Aᵀ = A) (hB : Bᵀ = B) (hM : M.Mem A)
    (hN : ∀ i j : Fin M.n, B i j ∈ N.get i j) : (A - B).PosDef :=
  posDef_of_pdCheck (M := M.sub N) h
    (by show (A - B : Matrix (Fin M.n) (Fin M.n) ℝ)ᵀ = _; rw [Matrix.transpose_sub, hA, hB])
    (mem_sub_imat hM hN)

theorem posDef_sub_of_lamMinGt {M : IMat} {s : Float} (h : lamMinGt M s = true)
    {A : Matrix (Fin M.n) (Fin M.n) ℝ} (hA : Aᵀ = A) (hM : M.Mem A) :
    (A - s.toReal • (1 : Matrix (Fin M.n) (Fin M.n) ℝ)).PosDef :=
  posDef_sub_of_lamMinCheck h hA hM

theorem posDef_sub_of_isGt {M N : IMat} (h : isGt M N = true)
    {A B : Matrix (Fin M.n) (Fin M.n) ℝ} (hA : Aᵀ = A) (hB : Bᵀ = B) (hM : M.Mem A)
    (hN : ∀ i j : Fin M.n, B i j ∈ N.get i j) : (A - B).PosDef :=
  posDef_sub_of_gtCheck h hA hB hM hN

end RealFP.Mat
