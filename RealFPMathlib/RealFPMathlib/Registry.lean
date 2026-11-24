/-
Extension registry: plug a new real function into every realfp tactic.

A user supplies (see `RealFPMathlib/Extensions/Erf.lean` for a complete example):

* the Mathlib-side function `f : ℝ → ℝ` (a constant, applied to one argument in goals);
* an `ExtFn` (core, Mathlib-free): the kernel enclosure `evK : KI → KI`, a domain test `domK`, and
  the derivative as an `IExpr` template in `var 0` (built-in functions only); a C fast path can be
  attached to `evK` with `@[implemented_by]`;
* a proof `ExtSound f D F` (enclosure, domain, derivative), tagged `@[realfp_fn]`.

The tactics then reify `f a` as `IExpr.ext k d a` (`k` a key derived from the `ExtFn`'s name),
and every proof they build is stated for an extension table built here from the registered
functions: `ExtTbl.ofList` (the enclosures, used by the kernel) and `ExtSem.ofList` (the real
functions and the user's soundness proofs). Nothing else is trusted: no axioms are added.
-/
import RealFPMathlib.IntervalSound
import RealFPMathlib.IntervalDeriv

open Lean Meta Elab Tactic
open Interval64 Interval64.KF

namespace RealFP

/-! ### Tables from lists -/

/-- The function with key `k` in `l` (first match), `ExtFn.none` if absent. -/
def lookupE (k : Nat) : List (Nat × ExtFn) → ExtFn
  | [] => ExtFn.none
  | (k', F) :: l => if k = k' then F else lookupE k l

/-- Extension table of a list of `(key, function)`. -/
@[reducible] def _root_.Interval64.KF.ExtTbl.ofList (l : List (Nat × ExtFn)) : ExtTbl := ⟨fun k => lookupE k l⟩

/-- The real function and domain with key `k` (parallel lists). -/
noncomputable def lookupR (k : Nat) : List (Nat × ExtFn) → List ((ℝ → ℝ) × (ℝ → Prop)) →
    (ℝ → ℝ) × (ℝ → Prop)
  | (k', _) :: l, q :: qs => if k = k' then q else lookupR k l qs
  | _, _ => (fun _ => 0, fun _ => False)

theorem lookup_sound : ∀ (l : List (Nat × ExtFn)) (qs : List ((ℝ → ℝ) × (ℝ → Prop))),
    List.Forall₂ (fun p q => ExtSound q.1 q.2 p.2) l qs →
    ∀ k, ExtSound (lookupR k l qs).1 (lookupR k l qs).2 (lookupE k l)
  | [], [], _, _ => extSound_none
  | (k', F) :: l, q :: qs, .cons h hs, k => by
    unfold lookupR lookupE
    split_ifs
    · exact h
    · exact lookup_sound l qs hs k

/-- Real semantics of `ExtTbl.ofList l`, from the soundness proofs `h`. -/
@[reducible] noncomputable def _root_.RealFP.ExtSem.ofList (l : List (Nat × ExtFn))
    (qs : List ((ℝ → ℝ) × (ℝ → Prop)))
    (h : List.Forall₂ (fun p q => ExtSound q.1 q.2 p.2) l qs) : @ExtSem (ExtTbl.ofList l) :=
  @ExtSem.mk (ExtTbl.ofList l) (fun k => (lookupR k l qs).1) (fun k => (lookupR k l qs).2)
    (lookup_sound l qs h)

theorem ExtSem.ofList_fn (l : List (Nat × ExtFn)) (qs : List ((ℝ → ℝ) × (ℝ → Prop))) (h)
    (k : Nat) : @ExtSem.fn _ (ExtSem.ofList l qs h) k = (lookupR k l qs).1 := rfl


/-! ### Monotone functions from rational point bounds

`ExtFn.ofMono fl fu m M` encloses a monotone `f` on `[a, b]` by `[fl a, fu b]` (rational lower
and upper bounds of `f` at the endpoints, `m`/`M` global bounds for infinite endpoints), rounded
outward to floats. `ExtSound.ofMono` proves it sound from the point bounds. -/

/-- Rational value of a bit pattern (`none` for `±∞`/NaN). -/
def ratOfBits (b : Nat) : Option ℚ := Spec.bitsToRat? (UInt64.ofNat b)

/-- Monotone extension from rational point bounds `fl ≤ f ≤ fu` and global bounds `m ≤ f ≤ M`. -/
def _root_.Interval64.KF.ExtFn.ofMono (name : String) (fl fu : ℚ → ℚ) (m M : ℚ)
    (domK : KI → Bool) (deriv : IExpr) : ExtFn where
  name := name
  evK X := KI.ofRatInterval ((ratOfBits X.lo).elim m fl) ((ratOfBits X.hi).elim M fu)
  domK := domK
  deriv := deriv

theorem le_of_mem_lo {X : KI} (hX : WF X) (hn : isNaN X.lo = false) {a : ℚ}
    (ha : ratOfBits X.lo = some a) {x : ℝ} (hx : x ∈ (toI X).toSet) : (a : ℝ) ≤ x := by
  have hb : Spec.bitsToRat? (toF X.lo).toBits = some a := by
    rw [toBits_toF_of_not_nan hX.1 hn]; exact ha
  have h := (mem_toSet_iff_toE.1 hx).1.2
  rw [show (toI X).lo = toF X.lo from rfl, toE_of_bitsToRat? hb] at h
  exact_mod_cast h

theorem ge_of_mem_hi {X : KI} (hX : WF X) (hn : isNaN X.hi = false) {b : ℚ}
    (hb : ratOfBits X.hi = some b) {x : ℝ} (hx : x ∈ (toI X).toSet) : x ≤ (b : ℝ) := by
  have hb' : Spec.bitsToRat? (toF X.hi).toBits = some b := by
    rw [toBits_toF_of_not_nan hX.2 hn]; exact hb
  have h := (mem_toSet_iff_toE.1 hx).2.2
  rw [show (toI X).hi = toF X.hi from rfl, toE_of_bitsToRat? hb'] at h
  exact_mod_cast h

theorem ExtSound.ofMono {f : ℝ → ℝ} {D : ℝ → Prop} {name : String} {fl fu : ℚ → ℚ} {m M : ℚ}
    {domK : KI → Bool} {deriv : IExpr} (hmono : Monotone f)
    (hl : ∀ q : ℚ, (fl q : ℝ) ≤ f q) (hu : ∀ q : ℚ, f q ≤ (fu q : ℝ))
    (hm : ∀ x, (m : ℝ) ≤ f x) (hM : ∀ x, f x ≤ (M : ℝ))
    (hdom : ∀ X : KI, WF X → isNaN X.lo = false → isNaN X.hi = false → domK X = true →
      ∀ x : ℝ, x ∈ (toI X).toSet → D x)
    (hfree : deriv.extFree = true) (hder : ∀ x, D x → HasDerivAt f (deriv.denoteB [x]) x) :
    ExtSound f D (ExtFn.ofMono name fl fu m M domK deriv) where
  enc X hX hlo hhi _ x hx := by
    show f x ∈ (toI (KI.ofRatInterval _ _)).toSet
    rw [(KF.ofRatInterval_toI _ _).1]
    apply mem_toSet_ofRatInterval
    · cases ha : ratOfBits X.lo with
      | none => exact hm x
      | some a => exact (hl a).trans (hmono (le_of_mem_lo hX hlo ha hx))
    · cases hb : ratOfBits X.hi with
      | none => exact hM x
      | some b => exact (hmono (ge_of_mem_hi hX hhi hb hx)).trans (hu b)
  dom := hdom
  deriv_extFree := hfree
  deriv := hder

/-! ### The registry -/

/-- A registered function: `fn` is the Mathlib function's head constant, `ext` the `ExtFn`
declaration, `sound` the `ExtSound` theorem, `key` the table key. -/
structure ExtEntry where
  fn : Name
  ext : Name
  sound : Name
  key : Nat
  deriving Inhabited, Repr

initialize extRegistry : SimplePersistentEnvExtension ExtEntry (Array ExtEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[] }

/-- Key of an `ExtFn` declaration (stable: a hash of its name). -/
def extKey (ext : Name) : Nat := ext.hash.toNat

/-- Read `ExtSound f D F` from a theorem's type. -/
def parseSound (thm : Name) : MetaM (Expr × Expr × Expr) := do
  let ty ← whnfR (← inferType (← mkConstWithLevelParams thm))
  match ty.getAppFnArgs with
  | (``ExtSound, #[f, D, F]) => return (f, D, F)
  | _ => throwError "realfp_fn: `{thm}` must prove `RealFP.ExtSound f D F`, but its type is{indentExpr ty}"

/-- `@[realfp_fn]` on a theorem `ExtSound f D F`: register `f` (a constant `ℝ → ℝ`) with the
kernel implementation `F` (a constant `ExtFn`) for all realfp tactics. -/
initialize registerBuiltinAttribute {
  name := `realfp_fn
  descr := "register a real function for the realfp tactics (on a theorem `RealFP.ExtSound f D F`)"
  add := fun thm _ kind => do
    unless kind == AttributeKind.global do throwError "realfp_fn: must be global"
    let (f, _, F) ← (parseSound thm).run' {} {}
    let some fn := f.constName? | throwError "realfp_fn: the function must be a constant, got {f}"
    let some ext := F.constName? | throwError "realfp_fn: the `ExtFn` must be a constant, got {F}"
    modifyEnv (extRegistry.addEntry · { fn, ext, sound := thm, key := extKey ext })
}

def registered : CoreM (Array ExtEntry) := do
  return extRegistry.getState (← getEnv)

def findEntry? (fn : Name) : CoreM (Option ExtEntry) := do
  return (← registered).reverse.find? (·.fn == fn)

unsafe def evalExtFnImpl (n : Name) : MetaM ExtFn := do
  match (← getEnv).evalConst ExtFn (← getOptions) n with
  | .ok F => return F
  | .error err => throwError "realfp: cannot evaluate the extension `{n}` natively: {err}"

/-- The `ExtFn` value of a registered declaration (for the native search). -/
@[implemented_by evalExtFnImpl]
opaque evalExtFn (n : Name) : MetaM ExtFn

/-- Runtime table (native search) of the given entries. -/
def runtimeTbl (es : Array ExtEntry) : MetaM ExtTbl := do
  let l ← es.toList.mapM fun e => return (e.key, ← evalExtFn e.ext)
  return ExtTbl.ofList l

/-! ### Proof-term context

The tactics build proofs whose constants take the instance arguments `[ExtTbl] [ExtSem]` first.
`withExtCtx es k` creates auxiliary definitions for the table and its semantics of the entries
`es` (when nonempty) and runs `k` with them recorded in the options; `mkC n` is `mkConst n`
applied to the current table and semantics (the empty defaults when there are no entries). -/

def optTbl : Name := `realfp.extTbl
def optSem : Name := `realfp.extSem
def optCount : Name := `realfp.extCount

/-- `ExtTbl` and `ExtSem` of the current proof context. -/
def ctxInsts : CoreM (Expr × Expr) := do
  let o ← getOptions
  let t : Name := o.get optTbl Name.anonymous
  let s : Name := o.get optSem Name.anonymous
  if t.isAnonymous then return (mkConst ``ExtTbl.empty, mkConst ``ExtSem.empty)
  return (mkConst t, mkConst s)

/-- `mkConst n` applied to the leading `[ExtTbl]` / `[ExtSem]` instance arguments. -/
def mkC (n : Name) : MetaM Expr := do
  let info ← getConstInfo n
  let c ← if info.levelParams.isEmpty then pure (mkConst n) else mkConstWithFreshMVarLevels n
  let (tblE, semE) ← ctxInsts
  let rec go (ty : Expr) (acc : Array Expr) : Array Expr :=
    match ty with
    | .forallE _ d b .instImplicit =>
      if d.isConstOf ``ExtTbl then go b (acc.push tblE)
      else if d.isAppOf ``ExtSem then go b (acc.push semE)
      else acc
    | _ => acc
  return mkAppN c (go info.type #[])

/-- Entries of the registered functions occurring in `e` (by head constant). -/
def entriesIn (e : Expr) : MetaM (Array ExtEntry) := do
  let es ← registered
  if es.isEmpty then return #[]
  let consts := e.getUsedConstants
  return es.filter fun en => consts.contains en.fn

/-- Run `k` in the proof context of the entries `es` (aux definitions for the table and its
semantics, built from the registered soundness theorems). -/
def withExtCtx {α} (es : Array ExtEntry) (k : TacticM α) : TacticM α := do
  if es.isEmpty then return ← k
  let pairT := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``Nat) (mkConst ``ExtFn)
  let lE ← mkListLit pairT (es.toList.map fun e =>
    mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) (mkConst ``Nat) (mkConst ``ExtFn) (toExpr e.key)
      (mkConst e.ext))
  let tblV := mkApp (mkConst ``ExtTbl.ofList) lE
  let tblN ← Term.mkAuxName `_realfp_extTbl
  let tblTy := mkConst ``ExtTbl
  addAndCompile <| Declaration.defnDecl
    { name := tblN, levelParams := [], type := tblTy, value := tblV, hints := ReducibilityHints.abbrev,
      safety := DefinitionSafety.safe }
  let rT ← mkArrow (mkConst ``Real) (mkConst ``Real)
  let dT ← mkArrow (mkConst ``Real) (mkSort 0)
  let qT := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) rT dT
  let mut qs := #[]
  let mut pfs := #[]
  for e in es do
    let (f, D, _) ← parseSound e.sound
    qs := qs.push (mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) rT dT f D)
    pfs := pfs.push (← mkConstWithLevelParams e.sound)
  let qsE ← mkListLit qT qs.toList
  -- `List.Forall₂ R l qs` by `cons` of the soundness theorems
  let R ← withLocalDeclD `p pairT fun p => withLocalDeclD `q qT fun q => do
    mkLambdaFVars #[p, q] (mkApp3 (mkConst ``ExtSound) (mkApp3 (mkConst ``Prod.fst [Level.zero, Level.zero]) rT dT q)
      (mkApp3 (mkConst ``Prod.snd [Level.zero, Level.zero]) rT dT q)
      (mkApp3 (mkConst ``Prod.snd [Level.zero, Level.zero]) (mkConst ``Nat) (mkConst ``ExtFn) p))
  let pairs := (es.toList.zip (qs.toList.zip pfs.toList))
  let rec mkF2 : List (ExtEntry × Expr × Expr) → MetaM (Expr × Expr × Expr)
    | [] => do
      let l0 ← mkListLit pairT []
      let q0 ← mkListLit qT []
      return (l0, q0, mkApp3 (mkConst ``List.Forall₂.nil [Level.zero, Level.zero]) pairT qT R)
    | (e, q, pf) :: rest => do
      let (lt, qt, h) ← mkF2 rest
      let p := mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) (mkConst ``Nat) (mkConst ``ExtFn) (toExpr e.key)
        (mkConst e.ext)
      let l' := mkApp3 (mkConst ``List.cons [Level.zero]) pairT p lt
      let q' := mkApp3 (mkConst ``List.cons [Level.zero]) qT q qt
      return (l', q', mkAppN (mkConst ``List.Forall₂.cons [Level.zero, Level.zero]) #[pairT, qT, R, p, q, lt, qt, pf, h])
  let (_, _, hE) ← mkF2 pairs
  let semV := mkApp3 (mkConst ``ExtSem.ofList) lE qsE hE
  let semTy := mkApp (mkConst ``ExtSem) (mkConst tblN)
  check semV
  let semN ← Term.mkAuxName `_realfp_extSem
  addDecl <| Declaration.defnDecl
    { name := semN, levelParams := [], type := semTy, value := semV, hints := ReducibilityHints.abbrev,
      safety := DefinitionSafety.safe }
  setReducibleAttribute semN
  setReducibleAttribute tblN
  -- `∀ x, ExtSem.fn key x = f x` for each entry (used to read reified goals back)
  for e in es, q in qs, i in [0:es.size] do
    let f := q.appFn!.appArg!
    let ty ← withLocalDeclD `x (mkConst ``Real) fun x => do
      mkForallFVars #[x] (← mkEq (mkApp4 (mkConst ``ExtSem.fn) (mkConst tblN) (mkConst semN)
        (toExpr e.key) x) (mkApp f x))
    let pf ← withLocalDeclD `x (mkConst ``Real) fun x => do
      mkLambdaFVars #[x] (← mkEqRefl (mkApp f x))
    addDecl <| Declaration.thmDecl
      { name := semN ++ Name.mkSimple s!"fn{i}", levelParams := [], type := ty, value := pf }
  withOptions (fun o => ((o.set optTbl tblN).set optSem semN).set optCount es.size) k

/-- Run a tactic with the registered functions occurring in the main goal or its hypotheses:
the native search gets their runtime table (instance argument), the proofs their aux table. -/
def withRegistered {α} (k : [ExtTbl] → TacticM α) : TacticM α := do
  let g ← getMainGoal
  let es ← g.withContext do
    let mut t ← instantiateMVars (← g.getType)
    for d in ← getLCtx do
      unless d.isImplementationDetail do t := mkApp t (← instantiateMVars d.type)
    entriesIn t
  if es.isEmpty then return ← @k ExtTbl.empty
  let tbl ← runtimeTbl es
  withExtCtx es (@k tbl)

/-- Simp lemmas `∀ x, ExtSem.fn key x = f x` of the current proof context. -/
def extSimpLemmas : CoreM (Array Name) := do
  let o ← getOptions
  let s : Name := o.get optSem Name.anonymous
  if s.isAnonymous then return #[]
  let n : Nat := o.get optCount 0
  return (List.range n).toArray.map fun i => s ++ Name.mkSimple s!"fn{i}"

end RealFP
