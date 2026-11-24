/-
`pos_def`: prove `M.PosDef` for a concrete real matrix `M : Matrix (Fin n) (Fin n) ℝ` with
rational (numeral) entries.

The entries are read off by `simp`/`norm_num`, a congruence certificate is computed natively
(`mkCert`, untrusted), and the checks `pdCheckL`, `ratMatOK` and symmetry are closed by
`decide +kernel` (or `native_decide` under `(trust := native)`). Soundness: `posDef_of_ratMat`.
-/
import RealFPMathlib.KMatrix
import RealFPMathlib.IntervalTactic
import RealFPMathlib.Trust

open Lean Meta Elab Tactic Interval64.KF Interval64.KF.KM

namespace RealFP.PosDefTactic

/-- Entry `(i, j)` of a list-of-rows rational matrix (0 outside). -/
def lget (L : List (List ℚ)) (i j : ℕ) : ℚ := (L.getD i []).getD j 0

theorem symm_of_check {n : ℕ} {f : ℕ → ℕ → ℚ}
    (h : ((List.range n).all fun i => (List.range n).all fun j => decide (f i j = f j i)) = true) :
    ∀ i j, i < n → j < n → f i j = f j i := by
  intro i j hi hj
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h i hi j hj

theorem posDef_of_eq {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℝ} (h : N.PosDef) (e : M = N) :
    M.PosDef := e ▸ h

/-- Close a fresh goal `ty` (a Boolean check `= true`) with the current trust mode. -/
def proveTrue (ty : Expr) : TacticM Expr := do
  let g ← mkFreshExprMVar ty
  let saved ← getGoals
  setGoals [g.mvarId!]
  closeCheck
  setGoals saved
  instantiateMVars g

def entryOf (M : Expr) (n i j : Nat) : MetaM ℚ := do
  let fin (k : Nat) : MetaM Expr := mkNumeral (mkApp (mkConst ``Fin) (mkNatLit n)) k
  let e := mkApp2 M (← fin i) (← fin j)
  let ctx ← Simp.mkContext (simpTheorems := #[← getSimpTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let r : Simp.Result ← (Mathlib.Meta.NormNum.deriveSimp ctx #[← Simp.getSimprocs] true e) <|> pure { expr := e }
  match ← RealFP.IntervalTactic.ratOf? r.expr with
  | some q => return q
  | none => throwError "pos_def: entry ({i}, {j}) of the matrix does not evaluate to a rational \
      numeral (got {r.expr})"

def provePosDef : TacticM Unit := withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  unless t.isAppOf ``Matrix.PosDef do throwError "pos_def: goal is not `Matrix.PosDef _`"
  let M := t.appArg!
  let_expr Matrix ι _ R := (← instantiateMVars (← inferType M))
    | throwError "pos_def: cannot read the matrix type"
  unless ← isDefEq R (mkConst ``Real) do throwError "pos_def: matrix is not over ℝ"
  let_expr Fin nE := (← whnfR ι) | throwError "pos_def: index type is not `Fin n`"
  let some n ← RealFP.IntervalTactic.natOf? nE | throwError "pos_def: size {nE} is not a numeral"
  let mut rows : List (List ℚ) := []
  for i in [0:n] do
    let mut row : List ℚ := []
    for j in [0:n] do
      row := row ++ [← entryOf M n i j]
    rows := rows ++ [row]
  let L := rows
  for i in [0:n] do
    for j in [0:n] do
      unless lget L i j == lget L j i do
        throwError "pos_def: the matrix is not symmetric (entries ({i}, {j}) and ({j}, {i}))"
  let A := ofRatFn n (lget L)
  let c := mkCert n A
  let fE := mkApp (mkConst ``lget) (toExpr L)
  let AE := toExpr A
  let cE := toExpr c
  let nL := mkNatLit n
  unless pdCheckL n A c do
    throwError "pos_def: the certificate check failed: the {n}×{n} matrix is not positive \
      definite, or too ill-conditioned for the binary64 congruence certificate"
  let h1 ← proveTrue (← mkEq (mkApp3 (mkConst ``pdCheckL) nL AE cE) (mkConst ``Bool.true))
  let h2 ← proveTrue (← mkEq (mkApp3 (mkConst ``ratMatOK) nL AE fE) (mkConst ``Bool.true))
  let rng ← mkAppM ``List.range #[nL]
  let inner ← withLocalDeclD `i (mkConst ``Nat) fun i => do
    let body ← withLocalDeclD `j (mkConst ``Nat) fun j => do
      mkLambdaFVars #[j] (← mkDecide (← mkEq (mkApp2 fE i j) (mkApp2 fE j i)))
    mkLambdaFVars #[i] (← mkAppM ``List.all #[rng, body])
  let symT ← mkEq (← mkAppM ``List.all #[rng, inner]) (mkConst ``Bool.true)
  let h3 ← proveTrue symT
  let hs ← mkAppOptM ``symm_of_check #[nL, fE, h3]
  let hpd ← mkAppOptM ``RealFP.KM.posDef_of_ratMat #[nL, AE, cE, fE, h1, h2, hs]
  let N := (← inferType hpd).appArg!
  let eG ← mkFreshExprMVar (← mkEq M N)
  let saved ← getGoals
  setGoals [eG.mvarId!]
  try
    evalTactic (← `(tactic| (ext i j; fin_cases i <;> fin_cases j <;>
      simp [lget, Matrix.of_apply] <;> norm_num)))
  catch ex =>
    throwError "pos_def: could not match the matrix with its rational entries: {ex.toMessageData}"
  setGoals saved
  let pf ← mkAppM ``posDef_of_eq #[hpd, ← instantiateMVars eG]
  (← getMainGoal).assign pf
  replaceMainGoal []

/-- `pos_def` proves `M.PosDef` for a concrete `n × n` real matrix with rational entries
(`!![2, 1; 1, 2]`, `Matrix.of fun i j => ...`). Option `(trust := native)`. -/
syntax (name := posDefTac) "pos_def" (ppSpace "(" ident " := " ident ")")? : tactic

@[tactic posDefTac] def evalPosDef : Tactic := fun stx => do
  let trust := if stx[1].getNumArgs > 0 then stx[1][3].getId else `inherit
  withTrust trust provePosDef

end RealFP.PosDefTactic
