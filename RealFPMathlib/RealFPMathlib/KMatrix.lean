/-
Soundness of the kernel PD certificate (`Interval64/Kernel/Matrix.lean`).

* `pdCheckK_of_pdCheckL` : the linear-time check (precomputed `T`, `B`) implies `pdCheckK`.
* `pdCheck_of_pdCheckK` : `pdCheckK n A X` is `pdCheck` on `toIMat n A` and the floats of `X`.
* `posDef_of_pdCheckL` / `posDef_of_pdCheckK` : every symmetric real `M` with
  `M i j ∈ toI (aget n A i j)` is positive definite.
* `memQK_sound`, `posDef_of_ratMat` : rational matrices (entry check `ratMatOK`).
-/
import RealFPMathlib.Matrix
import RealFPMathlib.IntervalSound
import Interval64.Kernel.MatrixCert

open Interval64 Interval64.KF Interval64.KF.KM Interval64.Mat Matrix
open Interval64Proofs.FloatBits Interval64.Spec

namespace RealFP.KM

open RealFP.Mat

/-! ### `pdCheckL → pdCheckK` (bit patterns only) -/

theorem idotK_congr {f f' g g' : ℕ → KI} {len : ℕ} (hf : ∀ k < len, f k = f' k)
    (hg : ∀ k < len, g k = g' k) : idotK f g len = idotK f' g' len := by
  induction len with
  | zero => rfl
  | succ k ih =>
    simp only [idotK]
    rw [ih (fun j hj => hf j (by omega)) (fun j hj => hg j (by omega)), hf k (by omega),
      hg k (by omega)]

theorem isumSkipK_congr {f f' : ℕ → KI} {s len : ℕ} (hf : ∀ k < len, f k = f' k) :
    isumSkipK f s len = isumSkipK f' s len := by
  induction len with
  | zero => rfl
  | succ k ih =>
    simp only [isumSkipK]
    rw [ih (fun j hj => hf j (by omega)), hf k (by omega)]

theorem getD_ofFnK {m : ℕ} {f : Fin m → KI} {k : ℕ} (hk : k < m) (d : KI) :
    (Array.ofFn f).getD k d = f ⟨k, hk⟩ := by
  simp [Array.getD, hk]

theorem tArrK_getD {n : ℕ} {A : Array KI} {X : Array ℕ} {i k : ℕ} (hi : i < n) (hk : k < n) :
    (tArrK n A X).getD (i * n + k) zeroK = tEntryK n A X i k := by
  rw [tArrK, getD_ofFnK (idx_lt hi hk)]; simp only [idx_div hk, idx_mod hk]

theorem bArrK_getD {n : ℕ} {A : Array KI} {X : Array ℕ} {i l : ℕ} (hi : i < n) (hl : l ≤ i) :
    (bArrK n A X).getD (i * n + l) zeroK = bEntryK n X (tArrK n A X) i l := by
  have hl' : l < n := by omega
  unfold bArrK
  rw [getD_ofFnK (idx_lt hi hl')]; simp only [idx_div hl', idx_mod hl', hl, ↓reduceIte]

theorem pdCheckK_of_pdCheckL {n : ℕ} {A : Array KI} {c : PDCert} (h : pdCheckL n A c = true) :
    pdCheckK n A c.X = true := by
  simp only [pdCheckL, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hA, hX⟩, hT⟩, hB⟩, hm⟩ := h
  simp only [tOK, bOK, List.all_eq_true, List.mem_range, beq_iff_eq] at hT hB
  have hT' : ∀ i < n, ∀ k < n, c.T.getD (i * n + k) zeroK = (tArrK n A c.X).getD (i * n + k) zeroK :=
    fun i hi k hk => by rw [hT i hi k hk, tArrK_getD hi hk]
  have hB' : ∀ i < n, ∀ l ≤ i, c.B.getD (i * n + l) zeroK = (bArrK n A c.X).getD (i * n + l) zeroK :=
    fun i hi l hl => by
      rw [hB i hi l (by omega), bArrK_getD hi hl]
      exact idotK_congr (fun k hk => hT' i hi k (by omega)) (fun _ _ => rfl)
  have hget : ∀ i < n, ∀ l < n, bgetK n c.B i l = bgetK n (bArrK n A c.X) i l := by
    intro i hi l hl
    unfold bgetK
    split
    · exact hB' i hi l (by omega)
    · exact hB' l hl i (by omega)
  simp only [pdCheckK, hA, hX, Bool.true_and, List.all_eq_true, List.mem_range] at hm ⊢
  intro i hi
  have e : marginK n c.B i = marginK n (bArrK n A c.X) i := by
    unfold marginK
    rw [hget i hi i hi, isumSkipK_congr (fun l hl => by rw [hget i hi l hl])]
  rw [← e]; exact hm i hi

/-! ### `pdCheckK → pdCheck` (via `toI`) -/

/-- The floats of `X`. -/
noncomputable def xF (n : ℕ) (X : Array ℕ) : FloatArray :=
  Interval64.FloatArray.ofFn (n * n) fun k => toF (X.getD k 0)

theorem toI_zeroK' : toI zeroK = Interval64.Mat.zeroI := toI_zeroK

theorem idotK_toI {f g : ℕ → KI} {F G : ℕ → Interval64} :
    ∀ len, (∀ k < len, WF (f k) ∧ toI (f k) = F k) → (∀ k < len, WF (g k) ∧ toI (g k) = G k) →
      WF (idotK f g len) ∧ toI (idotK f g len) = idot F G len
  | 0, _, _ => ⟨wf_zeroK, toI_zeroK'⟩
  | k + 1, hf, hg => by
    obtain ⟨h1, h2⟩ := idotK_toI k (fun j hj => hf j (by omega)) (fun j hj => hg j (by omega))
    obtain ⟨hf1, hf2⟩ := hf k (by omega)
    obtain ⟨hg1, hg2⟩ := hg k (by omega)
    simp only [idotK, idot]
    refine ⟨add_wf h1 (mul_wf hf1 hg1), ?_⟩
    rw [add_toI h1 (mul_wf hf1 hg1), mul_toI hf1 hg1, h2, hf2, hg2]

theorem isumSkipK_toI {f : ℕ → KI} {F : ℕ → Interval64} {s : ℕ} :
    ∀ len, (∀ k < len, WF (f k) ∧ toI (f k) = F k) →
      WF (isumSkipK f s len) ∧ toI (isumSkipK f s len) = isumSkip F s len
  | 0, _ => ⟨wf_zeroK, toI_zeroK'⟩
  | k + 1, hf => by
    obtain ⟨h1, h2⟩ := isumSkipK_toI (s := s) k (fun j hj => hf j (by omega))
    obtain ⟨hf1, hf2⟩ := hf k (by omega)
    simp only [isumSkipK, isumSkip]
    split
    · exact ⟨h1, h2⟩
    · exact ⟨add_wf h1 hf1, by rw [add_toI h1 hf1, h2, hf2]⟩

section
variable {n : ℕ} {A : Array KI} {X : Array ℕ}

theorem aget_wf (hA : wfA A = true) (i j : ℕ) : WF (aget n A i j) := by
  unfold aget Array.getD
  split
  · rename_i h
    simp only [wfA, Array.all_eq_true] at hA
    have := hA _ h
    simp only [Bool.and_eq_true, Nat.blt_eq] at this
    exact ⟨this.1, this.2⟩
  · exact wf_zeroK

theorem toIMat_get {i j : ℕ} (hi : i < n) (hj : j < n) :
    (toIMat n A).get i j = toI (aget n A i j) := by
  rw [toIMat, get_ofFn hi hj]; rfl

theorem fget_xF {i j : ℕ} (hi : i < n) (hj : j < n) :
    fget (xF n X) (i * n + j) = toF (X.getD (i * n + j) 0) := by
  rw [xF, fget_ofFn (idx_lt hi hj)]

theorem xFin_wf (hX : xFiniteK n X = true) {i j : ℕ} (hi : i < n) (hj : j ≤ i) :
    X.getD (i * n + j) 0 < 2 ^ 64 ∧ isNaN (X.getD (i * n + j) 0) = false ∧
      isInf (X.getD (i * n + j) 0) = false := by
  simp only [xFiniteK, List.all_eq_true, List.mem_range, Bool.and_eq_true, Nat.blt_eq,
    Bool.not_eq_true'] at hX
  obtain ⟨⟨h1, h2⟩, h3⟩ := hX i hi j (by omega)
  exact ⟨h1, h2, h3⟩

theorem xent_toI (hX : xFiniteK n X = true) {i j : ℕ} (hi : i < n) (hj : j ≤ i) :
    WF (xentK n X i j) ∧ toI (xentK n X i j) = xent n (xF n X) i j := by
  obtain ⟨h1, -, -⟩ := xFin_wf hX hi hj
  refine ⟨⟨h1, h1⟩, ?_⟩
  simp only [xentK, xent, fget_xF hi (by omega : j < n)]; rfl

theorem xFinite_xF (hX : xFiniteK n X = true) : xFinite n (xF n X) = true := by
  simp only [xFinite, List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true']
  intro i hi j hj
  obtain ⟨h1, h2, h3⟩ := xFin_wf hX hi (by omega : j ≤ i)
  rw [fget_xF hi (by omega), isNaN_toF h1, isInf_toF h1, h2, h3]
  simp

theorem tEntry_toI (hA : wfA A = true) (hX : xFiniteK n X = true) {i k : ℕ} (hi : i < n)
    (hk : k < n) : WF (tEntryK n A X i k) ∧
      toI (tEntryK n A X i k) = tEntry (toIMat n A) (xF n X) i k :=
  idotK_toI (i + 1) (fun j hj => xent_toI hX hi (by omega))
    (fun j hj => ⟨aget_wf hA j k, (toIMat_get (by omega) hk).symm⟩)

theorem tArr_toI (hA : wfA A = true) (hX : xFiniteK n X = true) {i k : ℕ} (hi : i < n)
    (hk : k < n) : WF ((tArrK n A X).getD (i * n + k) zeroK) ∧
      toI ((tArrK n A X).getD (i * n + k) zeroK) =
        (tArr (toIMat n A) (xF n X)).getD (i * n + k) Interval64.Mat.zeroI := by
  have e : (toIMat n A).n = n := rfl
  rw [tArrK_getD hi hk, tArr,
    getD_ofFn (m := (toIMat n A).n * (toIMat n A).n) (k := i * n + k) (idx_lt hi hk)]
  simp only [e, idx_div hk, idx_mod hk]
  exact tEntry_toI hA hX hi hk

theorem bArr_toI (hA : wfA A = true) (hX : xFiniteK n X = true) {i l : ℕ} (hi : i < n)
    (hl : l ≤ i) : WF ((bArrK n A X).getD (i * n + l) zeroK) ∧
      toI ((bArrK n A X).getD (i * n + l) zeroK) =
        (bArr (toIMat n A) (xF n X)).getD (i * n + l) Interval64.Mat.zeroI := by
  have hl' : l < n := by omega
  have e : (toIMat n A).n = n := rfl
  rw [bArrK_getD hi hl]
  unfold bArr
  simp only
  rw [getD_ofFn (m := (toIMat n A).n * (toIMat n A).n) (k := i * n + l) (idx_lt hi hl')]
  simp only [e, idx_div hl', idx_mod hl', hl, ↓reduceIte]
  exact idotK_toI (l + 1) (fun k hk => tArr_toI hA hX hi (by omega))
    (fun k hk => xent_toI hX hl' (by omega))

theorem bget_toI (hA : wfA A = true) (hX : xFiniteK n X = true) {i l : ℕ} (hi : i < n)
    (hl : l < n) : WF (bgetK n (bArrK n A X) i l) ∧
      toI (bgetK n (bArrK n A X) i l) = bget n (bArr (toIMat n A) (xF n X)) i l := by
  unfold bgetK bget
  split
  · exact bArr_toI hA hX hi (by omega)
  · exact bArr_toI hA hX hl (by omega)

theorem margin_toI (hA : wfA A = true) (hX : xFiniteK n X = true) {i : ℕ} (hi : i < n) :
    toI (marginK n (bArrK n A X) i) = margin n (bArr (toIMat n A) (xF n X)) i := by
  obtain ⟨h1, h2⟩ := bget_toI hA hX hi hi
  obtain ⟨h3, h4⟩ := isumSkipK_toI (s := i) n (fun l hl =>
    ⟨abs_wf (bget_toI hA hX hi hl).1, by rw [abs_toI (bget_toI hA hX hi hl).1, (bget_toI hA hX hi hl).2]⟩)
  unfold marginK margin
  rw [sub_toI h1 h3, h2, h4]

theorem margin_wf (hA : wfA A = true) (hX : xFiniteK n X = true) {i : ℕ} (hi : i < n) :
    WF (marginK n (bArrK n A X) i) := by
  obtain ⟨h1, -⟩ := bget_toI hA hX hi hi
  obtain ⟨h3, -⟩ := isumSkipK_toI (s := i) n (fun l hl =>
    ⟨abs_wf (bget_toI hA hX hi hl).1, by rw [abs_toI (bget_toI hA hX hi hl).1, (bget_toI hA hX hi hl).2]⟩)
  exact sub_wf h1 h3

theorem pdCheck_of_pdCheckK (h : pdCheckK n A X = true) : pdCheck (toIMat n A) (xF n X) = true := by
  simp only [pdCheckK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hA, hX⟩, hm⟩ := h
  simp only [pdCheck, Bool.and_eq_true]
  refine ⟨xFinite_xF hX, ?_⟩
  simp only [marginsPos, List.all_eq_true, List.mem_range]
  intro i hi
  have hfi : fget (pdMargins (toIMat n A) (xF n X)) (2 * i) =
      (margin n (bArr (toIMat n A) (xF n X)) i).lo :=
    fget_pdMargins (M := toIMat n A) ⟨i, hi⟩
  rw [hfi, ← margin_toI hA hX hi]
  have := lt_toF zero_lt (margin_wf hA hX hi).1
  rw [hm i hi] at this
  rw [← toF_zero]; exact this

end

/-! ### Real conclusions -/

/-- **Kernel PD certificate.** -/
theorem posDef_of_pdCheckK {n : ℕ} {A : Array KI} {X : Array ℕ} (h : pdCheckK n A X = true)
    {M : Matrix (Fin n) (Fin n) ℝ} (hs : Mᵀ = M) (hM : ∀ i j : Fin n, M i j ∈ toI (aget n A i j)) :
    M.PosDef :=
  posDef_of_pdCheck (M := toIMat n A) (pdCheck_of_pdCheckK h) hs fun i j => by
    have := hM i j
    rw [← toIMat_get (n := n) (A := A) (show (i : ℕ) < n from i.2) (show (j : ℕ) < n from j.2)] at this
    exact this

/-- **Kernel PD certificate, linear-time form** (`pd_certs% n A` supplies `c`). -/
theorem posDef_of_pdCheckL {n : ℕ} {A : Array KI} {c : PDCert} (h : pdCheckL n A c = true)
    {M : Matrix (Fin n) (Fin n) ℝ} (hs : Mᵀ = M) (hM : ∀ i j : Fin n, M i j ∈ toI (aget n A i j)) :
    M.PosDef :=
  posDef_of_pdCheckK (pdCheckK_of_pdCheckL h) hs hM

theorem memQK_sound {q : ℚ} {a : KI} (h : memQK q a = true) : (q : ℝ) ∈ toI a := by
  simp only [memQK, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, hn1⟩, hn2⟩, h3⟩ := h
  split at h3
  · rename_i l u hl hu
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
    have hl' : bitsToRat? (toF a.lo).toBits = some l := by rw [toBits_toF_of_not_nan h1 hn1]; exact hl
    have hu' : bitsToRat? (toF a.hi).toBits = some u := by rw [toBits_toF_of_not_nan h2 hn2]; exact hu
    refine mem_toSet_of_toE (I := toI a) ((isNaN_toF h1).trans hn1) ((isNaN_toF h2).trans hn2) ?_ ?_
    · show (toF a.lo).toE ≤ _
      rw [toE_of_bitsToRat? hl']; exact EReal.coe_le_coe_iff.2 (by exact_mod_cast h3.1)
    · show _ ≤ (toF a.hi).toE
      rw [toE_of_bitsToRat? hu']; exact EReal.coe_le_coe_iff.2 (by exact_mod_cast h3.2)
  · simp at h3

/-- **Rational matrices**: `ratMatOK n A f` and the PD certificate give `PosDef` of the real
    matrix `(f i j : ℝ)`. -/
theorem posDef_of_ratMat {n : ℕ} {A : Array KI} {c : PDCert} {f : ℕ → ℕ → ℚ}
    (h : pdCheckL n A c = true) (hf : ratMatOK n A f = true)
    (hs : ∀ i j, i < n → j < n → f i j = f j i) :
    (Matrix.of fun i j : Fin n => (f i j : ℝ)).PosDef := by
  refine posDef_of_pdCheckL h ?_ fun i j => ?_
  · ext i j; simp [hs i j i.2 j.2]
  · simp only [ratMatOK, List.all_eq_true, List.mem_range] at hf
    exact memQK_sound (hf i i.2 j j.2)

/-- Every eigenvalue of `A` exceeds `s` when `A - s • 1` is positive definite. -/
theorem lt_eigenvalue_of_posDef_sub {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {s : ℝ}
    (h : (A - s • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef) {μ : ℝ}
    (hμ : Module.End.HasEigenvalue (Matrix.toLin' A) μ) : s < μ := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hAv : A *ᵥ v = μ • v := by
    have := Module.End.mem_eigenspace_iff.1 hv.1
    rwa [Matrix.toLin'_apply] at this
  have hlt := (posDef_iff_dotProduct_mulVec.1 h).2 hv.2
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, hAv] at hlt
  have hd : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  by_contra hc
  push Not at hc
  nlinarith

end RealFP.KM
