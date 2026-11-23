/-
Soundness of the shared-subexpression Taylor quadrature `KF.KQ.quadKS` / `quadBoundS`:
under `shareOK` it computes exactly `quadK` (`quadKS_some`), so `integral_mem_quadK` applies.

* `evalK_subst` : `evalK env (e.subst σ) = evalK env' e` when `σ i` evaluates to `env'[i]`.
* `lets_inv` : the let values are the evaluations of their expansions.
* `integral_bounds_of_quadBoundS` : rigorous bounds from a kernel-checked `quadBoundS`.
-/
import RealFPMathlib.KQuad
import Interval64.Kernel.QuadShare

open Interval64 Interval64.KF Interval64.KF.KQ Set intervalIntegral MeasureTheory

noncomputable section

namespace RealFP.KQS

open RealFP RealFP.KQ

theorem evalK_subst {env env' : List KI} {σ : Nat → IExpr} {n : Nat}
    (h : ∀ i < n, evalK env (σ i) = env'.getD i zeroK) :
    ∀ e : IExpr, e.varsLt n = true → evalK env (e.subst σ) = evalK env' e := by
  intro e
  induction e <;> intro hv <;>
    simp_all [IExpr.subst, IExpr.varsLt, evalK, Nat.blt_eq]

theorem getD_append_lt {α : Type} {l : List α} {x d : α} {i : Nat} (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_append_eq {α : Type} {l : List α} {x d : α} :
    (l ++ [x]).getD l.length d = x := by
  simp [List.getD_eq_getElem?_getD]

theorem lets_inv (env : List KI) :
    ∀ (lets : List IExpr) (accE : List IExpr) (accV : List KI), accE.length = accV.length →
      (∀ i < accE.length, accV.getD i zeroK = evalK env (accE.getD i (.var 0))) →
      letsOK accE.length lets = true →
      (lets.foldl (fun acc d => acc ++ [d.subst fun i => acc.getD i (.var 0)]) accE).length =
          (lets.foldl (fun acc d => acc ++ [evalK acc d]) accV).length ∧
        ∀ i < (lets.foldl (fun acc d => acc ++ [d.subst fun i => acc.getD i (.var 0)]) accE).length,
          (lets.foldl (fun acc d => acc ++ [evalK acc d]) accV).getD i zeroK =
            evalK env ((lets.foldl (fun acc d => acc ++ [d.subst fun i => acc.getD i (.var 0)])
              accE).getD i (.var 0))
  | [], accE, accV, hl, hi, _ => ⟨hl, hi⟩
  | d :: ds, accE, accV, hl, hi, hok => by
    simp only [letsOK, Bool.and_eq_true] at hok
    simp only [List.foldl_cons]
    refine lets_inv env ds _ _ (by simp [hl]) ?_ (by simpa using hok.2)
    intro i hi'
    simp only [List.length_append, List.length_singleton] at hi'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with h | h
    · rw [getD_append_lt h, getD_append_lt (hl ▸ h)]; exact hi i h
    · subst h
      rw [getD_append_eq, hl, getD_append_eq]
      exact (evalK_subst (env' := accV) (fun i hi2 => (hi i hi2).symm) d hok.1).symm

theorem evalLets_spec {X : KI} {lets : List IExpr} (hok : letsOK 1 lets = true) :
    (expLets lets).length = (evalLets [X] lets).length ∧
      ∀ i < (expLets lets).length,
        (evalLets [X] lets).getD i zeroK = evalK [X] ((expLets lets).getD i (.var 0)) :=
  lets_inv [X] lets [.var 0] [X] rfl
    (fun i hi => by
      simp only [List.length_singleton, Nat.lt_one_iff] at hi
      subst hi; rfl) hok

/-- A well-scoped root evaluates on the let environment like its expansion on `[X]`. -/
theorem evalK_root {X : KI} {lets : List IExpr} (hok : letsOK 1 lets = true) {r : IExpr}
    (hr : r.varsLt (lets.length + 1) = true) :
    evalK (evalLets [X] lets) r = evalK [X] (r.subst fun i => (expLets lets).getD i (.var 0)) := by
  have hs := evalLets_spec (X := X) hok
  have hlen : (expLets lets).length = lets.length + 1 := by
    unfold expLets
    suffices ∀ (l : List IExpr) (acc : List IExpr),
        (l.foldl (fun acc d => acc ++ [d.subst fun i => acc.getD i (.var 0)]) acc).length =
          acc.length + l.length by simpa [Nat.add_comm] using this lets [.var 0]
    intro l; induction l with
    | nil => simp
    | cons d l ih => intro acc; rw [List.foldl_cons, ih]; simp; omega
  refine (evalK_subst (n := lets.length + 1) (fun i hi => ?_) r hr).symm
  exact (hs.2 i (hlen ▸ hi)).symm

theorem taylorKS_eq {n lo m hi : Nat} {envM : List KI} {σ : Nat → IExpr}
    (hev : ∀ r : IExpr, r.varsLt n = true → evalK envM r = evalK [pt m] (r.subst σ)) :
    ∀ (roots : List IExpr) (j : Nat), roots.all (IExpr.varsLt n) = true →
      taylorKS lo m hi envM j roots = taylorK lo m hi j (roots.map (IExpr.subst σ))
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | r :: r' :: rs, j, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.map_cons, taylorKS, taylorK]
    rw [hev r h.1]
    have := taylorKS_eq (lo := lo) (hi := hi) hev (r' :: rs) (j + 1) (by simp [h.2.1, h.2.2])
    simp only [List.map_cons] at this
    rw [this]

theorem getLastD_map {α β : Type} (f : α → β) {l : List α} (hl : l ≠ []) (x : α) (y : β) :
    (l.map f).getLastD y = f (l.getLastD x) := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l => simpa using ih (by simp)

theorem getLastD_ne {α : Type} {l : List α} (hl : l ≠ []) (x y : α) : l.getLastD x = l.getLastD y := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a l ih => cases l with
    | nil => rfl
    | cons b l => simpa using ih (by simp)

theorem getLastD_mem {α : Type} {l : List α} (hl : l ≠ []) (x : α) : l.getLastD x ∈ l := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a l ih => cases l with
    | nil => simp [List.getLastD]
    | cons b l =>
      have := ih (by simp)
      have e : (a :: b :: l).getLastD x = (b :: l).getLastD x := by simp [List.getLastD]
      rw [e]; exact List.mem_cons_of_mem _ this

theorem quadKS_some {e : IExpr} {K a b : Nat} {cs : List (Nat × Nat × Nat)} {lets roots : List IExpr}
    {R : KI} (h : quadKS e K a b cs lets roots = some R) : quadK e K a b cs = some R := by
  unfold quadKS at h
  dsimp only at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨hsh, h2⟩, h0⟩, hch⟩, hall⟩ := hc
    cases Option.some.inj h
    simp only [shareOK, Bool.and_eq_true, decide_eq_true_eq] at hsh
    obtain ⟨⟨hlets, hroots⟩, heq⟩ := hsh
    set σ := fun i => (expLets lets).getD i (.var 0)
    have hne : roots ≠ [] := by
      intro h0; rw [h0] at heq; exact derivs_ne_nil e K (by simpa using heq.symm)
    unfold quadK
    dsimp only
    rw [ite_eq_left_of_eq_true _ _ (by simp [h2, h0, hch, hall])]
    congr 1
    have hcell : ∀ c : Nat × Nat × Nat,
        cellKS lets roots K (derivs e K) c = cellK (derivs e K) K ((derivs e K).getLastD e) c := by
      intro c
      have ht := taylorKS_eq (lo := c.1) (m := c.2.1) (hi := c.2.2) (σ := σ)
        (fun r hr => evalK_root hlets hr) roots 0 hroots
      rw [heq] at ht
      have hr0 := List.all_eq_true.1 hroots _ (getLastD_mem hne (.var 0))
      have hrem : evalK (evalLets [⟨c.1, c.2.2⟩] lets) (roots.getLastD ((derivs e K).getLastD (.var 0))) =
          evalK [⟨c.1, c.2.2⟩] ((derivs e K).getLastD e) := by
        rw [getLastD_ne hne _ (.var 0), evalK_root hlets hr0, ← heq, getLastD_map _ hne (.var 0)]
      unfold cellKS cellK remK
      rw [ht, hrem]
    have hsum : ∀ cs' : List (Nat × Nat × Nat),
        sumCellsS lets roots K (derivs e K) cs' = sumCells (derivs e K) K ((derivs e K).getLastD e) cs' := by
      intro cs'; induction cs' with
      | nil => rfl
      | cons c cs' ih => simp only [sumCellsS, sumCells, hcell, ih]
    rw [hsum]
  · exact absurd h (by simp)


/-- **Rigorous integral bounds** from a kernel-checked `quadBoundS` (shared-subexpression)
    certificate. -/
theorem integral_bounds_of_quadBoundS {e : IExpr} {K a b : Nat} {cs : List (Nat × Nat × Nat)}
    {lets roots : List IExpr} {qa qb ql qh : ℚ}
    (h : quadBoundS e K a b cs lets roots qa qb ql qh = true) :
    (ql : ℝ) ≤ (∫ x in (qa : ℝ)..qb, e.denote [x]) ∧
      (∫ x in (qa : ℝ)..qb, e.denote [x]) ≤ qh := by
  unfold quadBoundS at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨ha, hb⟩, h⟩ := h
  split at h
  · rename_i R hR
    obtain ⟨hm, -⟩ := integral_mem_quadK (quadKS_some hR) (ratOf_sound ha).2.2 (ratOf_sound hb).2.2
    obtain ⟨⟨-, h1⟩, ⟨-, h2⟩⟩ := mem_toSet_iff_toE.1 hm
    split at h
    · rename_i l u hl hu
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have h1' := (ratOf_sound hl).2.2
      have h2' := (ratOf_sound hu).2.2
      simp only [toI] at h1 h2
      rw [h1'] at h1; rw [h2'] at h2
      exact ⟨le_trans (by exact_mod_cast h.1) (EReal.coe_le_coe_iff.1 h1),
        le_trans (EReal.coe_le_coe_iff.1 h2) (by exact_mod_cast h.2)⟩
    · simp at h
  · simp at h

/-! ### Witnessed let values (`quadKW`) -/

theorem keq_eq {a b : KI} (h : keq a b = true) : a = b := by
  simp only [keq, Bool.and_eq_true, Nat.beq_eq] at h
  cases a; cases b; simp_all

theorem letsW_spec : ∀ (acc : List KI) (lets : List IExpr) (vs : List KI),
    letsW acc lets vs = true → evalLets acc lets = acc ++ vs
  | acc, [], [], _ => by simp [evalLets]
  | acc, d :: ds, v :: vs, h => by
    simp only [letsW, Bool.and_eq_true] at h
    have hv := keq_eq h.1
    have ih := letsW_spec (acc ++ [v]) ds vs h.2
    show evalLets (acc ++ [evalK acc d]) ds = _
    rw [hv, ih]; simp
  | _, [], _ :: _, h => by simp [letsW] at h
  | _, _ :: _, [], h => by simp [letsW] at h

theorem sumCellsW_eq {roots lets : List IExpr} {K : Nat} {ds : List IExpr} :
    ∀ (cs : List (Nat × Nat × Nat)) (ws : List (List KI × List KI)), cellsW lets cs ws = true →
      sumCellsW roots K ds cs ws = sumCellsS lets roots K ds cs
  | [], [], _ => rfl
  | c :: cs, w :: ws, h => by
    simp only [cellsW, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    simp only [sumCellsW, sumCellsS, sumCellsW_eq cs ws h3, cellKW, cellKS,
      letsW_spec _ _ _ h1, letsW_spec _ _ _ h2, List.singleton_append]
  | [], _ :: _, h => by simp [cellsW] at h
  | _ :: _, [], h => by simp [cellsW] at h

theorem quadKW_some {e : IExpr} {K a b : Nat} {cs : List (Nat × Nat × Nat)} {lets roots : List IExpr}
    {ws : List (List KI × List KI)} {R : KI} (h : quadKW e K a b cs lets roots ws = some R) :
    quadKS e K a b cs lets roots = some R := by
  unfold quadKW at h
  dsimp only at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨hc, hw⟩ := hc
    unfold quadKS
    dsimp only
    rw [if_pos (by simpa only [Bool.and_eq_true] using hc), ← sumCellsW_eq cs ws hw]
    exact h
  · exact absurd h (by simp)

/-- **Rigorous integral bounds** from a kernel-checked `quadBoundW` (shared subexpressions with
    witnessed let values) certificate. -/
theorem integral_bounds_of_quadBoundW {e : IExpr} {K a b : Nat} {cs : List (Nat × Nat × Nat)}
    {lets roots : List IExpr} {ws : List (List KI × List KI)} {qa qb ql qh : ℚ}
    (h : quadBoundW e K a b cs lets roots ws qa qb ql qh = true) :
    (ql : ℝ) ≤ (∫ x in (qa : ℝ)..qb, e.denote [x]) ∧
      (∫ x in (qa : ℝ)..qb, e.denote [x]) ≤ qh := by
  apply integral_bounds_of_quadBoundS (lets := lets) (roots := roots) (cs := cs) (K := K) (a := a) (b := b)
  unfold quadBoundW at h
  unfold quadBoundS
  revert h
  cases hq : quadKW e K a b cs lets roots ws with
  | none => simp
  | some R => rw [quadKW_some hq]; exact id

end RealFP.KQS
