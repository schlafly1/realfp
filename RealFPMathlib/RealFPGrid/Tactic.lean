import RealFPGrid.Sound

/-! # `interval_grid`: many-box proofs with an optional GPU search

```
example : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1, x * y - x ^ 2 ≤ 1 / 4 := by
  interval_grid
```

Goal shapes: `f ≤ c`, `c ≤ f`, `f ≤ g` (as `f - g ≤ 0`), `f ≥ …`, conjunctions; the variables
bounded by rational numerals in the context (as for realfp's `interval`). The proof is
`RealFP.Grid.prove_le` / `prove_ge` with one `native_decide` (the C checker
`c/grid_tape.c`): plain bisection, no derivatives, so it suits problems that need very many boxes
of the same kind (see `docs/GPU.md` for when to use it instead of `interval`).

The certificate (untrusted) comes from, in order:
1. the cache file given by `(cert := "file")` if it exists and was made for the same problem;
2. the `realfp-grid` tool (`grid/`, CUDA or multithreaded CPU), if found: `$REALFP_GRID`, then
   `realfp-grid` on `PATH`, then `grid/build/realfp-grid` in the realfp checkout;
3. the built-in single-threaded search (`RealFP.Grid.searchGrid`).

Options: `(cert := "file")` (path relative to the current file; written after a search),
`(tool := auto | none | cpu | gpu | gpu32 | gpu64)` (`none`: built-in search only),
`(depth := n)` (levels; default 30 per variable), `(maxBoxes := n)` (default 10⁹ for the tool,
10⁷ built in), `(explore := true)` (do not prove: report an enclosure of the extremum, then fail),
`(export := "file")` (write the tool's problem file and stop, for the command-line workflow),
`(use := thm)` (close the goal with a theorem `∀ xs, InBoxes xs bs → e.denote xs ≤ c`, e.g. one
assembled from split certificates by `grid/gen_lean.py`).

Strict inequalities are not supported (tighten the bound by a little instead). -/

open Lean Meta Elab Tactic
open Interval64 Interval64.KF RealFP.IntervalTactic

namespace RealFP.Grid.Tac

structure GCfg where
  depth : Nat := 0
  maxBoxes : Nat := 0
  tool : Name := `auto
  cert : Option String := none
  explore : Bool := false
  export? : Option String := none
  use? : Option Name := none

declare_syntax_cat gridOpt
syntax "(" ident " := " num ")" : gridOpt
syntax "(" ident " := " ident ")" : gridOpt
syntax "(" ident " := " str ")" : gridOpt

/-- FNV-1a 64 of a string (cache key; same as the tool's). -/
def fnv (s : String) : UInt64 :=
  s.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211) 14695981039346656037

def hexU64 (x : UInt64) : String := hex16 x.toNat

/-- The file next to the current Lean file. -/
def relPath (p : String) : MetaM System.FilePath := do
  if p.startsWith "/" then return p
  let dir := (← getFileName) |> System.FilePath.mk |>.parent |>.getD "."
  return dir / p

/-- `realfp-grid`, if installed. -/
def findTool : IO (Option String) := do
  if let some p ← IO.getEnv "REALFP_GRID" then
    if ← System.FilePath.pathExists p then return some p
  if let some path ← IO.getEnv "PATH" then
    for d in path.splitOn ":" do
      let p := System.FilePath.mk d / "realfp-grid"
      if ← p.pathExists then return some p.toString
  -- the realfp checkout: this module's olean is in <realfp>/RealFPMathlib/.lake/build/lib/lean
  let sp ← Lean.searchPathRef.get
  for d in sp do
    for up in [["..", "..", "..", "..", ".."], ["..", "..", "..", "..", "..", "..", "..", ".."]] do
      let p := up.foldl (· / ·) d / "grid" / "build" / "realfp-grid"
      if ← p.pathExists then return some p.toString
  return none

/-- The certificate line (the first line that is not empty and not a comment) and the problem
fingerprint recorded in the header, if any. -/
def readCert (p : System.FilePath) : IO (Option String × String) := do
  let txt ← IO.FS.readFile p
  let ls := txt.splitOn "\n"
  let key := ls.findSome? fun l =>
    if l.startsWith "# problem fnv " then some (l.drop 14).toString.trimAscii.toString else none
  let line := ls.filter (fun l => !l.startsWith "#" && !l.isEmpty) |>.headD ""
  return (key, line)

def runTool (tool : String) (args : Array String) : IO (UInt32 × String) := do
  let out ← IO.Process.output { cmd := tool, args := args }
  return (out.exitCode, out.stdout ++ out.stderr)

/-- Lean source of an `IExpr` (for `(export := …)`). -/
partial def iexprSrc : IExpr → Except String String
  | .var i => .ok s!"(.var {i})"
  | .rat q => .ok s!"(.rat ({q.num} / {q.den}))"
  | .add a b => do .ok s!"(.add {← iexprSrc a} {← iexprSrc b})"
  | .sub a b => do .ok s!"(.sub {← iexprSrc a} {← iexprSrc b})"
  | .mul a b => do .ok s!"(.mul {← iexprSrc a} {← iexprSrc b})"
  | .div a b => do .ok s!"(.div {← iexprSrc a} {← iexprSrc b})"
  | .neg a => do .ok s!"(.neg {← iexprSrc a})"
  | .sqrt a => do .ok s!"(.sqrt {← iexprSrc a})"
  | .pow a n => do .ok s!"(.pow {← iexprSrc a} {n})"
  | _ => .error "only + - * / neg sqrt and natural powers can be exported"

def ratSrc (q : ℚ) : String := s!"({q.num} / {q.den} : Rat)"

def proveLe (cfg : GCfg) (lhs rhs : Expr) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
  let (f, c, upper) ← do
    if let some c ← ratOf? rhs then pure (lhs, c, true)
    else if let some c ← ratOf? lhs then pure (rhs, c, false)
    else
      let gs ← goal.apply (mkConst ``le_of_sub)
      replaceMainGoal gs
      pure (← mkAppM ``HSub.hSub #[lhs, rhs], (0 : ℚ), true)
  let goal ← getMainGoal
  goal.withContext do
  let vars ← collectVars f
  let e ← reify vars f
  let bs ← vars.mapM (fun v => (findBounds v : MetaM (ℚ × ℚ)))
  let d := vars.size
  let fe := compile e
  let envK := boxes bs.toList
  let env := envK.map toIC
  let cK := KI.ofRat c
  let cb := if upper then cK.lo else cK.hi
  let prob? := problemText fe upper cb env
  let depth := if cfg.depth == 0 then min 1000 (30 * d) else cfg.depth
  let eE := iexprToExpr e
  let bsE := toExpr bs.toList
  let cE := toExpr c
  let xsE ← mkListLit (mkConst ``Real) vars.toList
  let saved ← getGoals
  let hxsM ← mkFreshExprMVar (mkApp2 (mkConst ``InBoxes) xsE bsE)
  -- (use := thm): an existing theorem
  if let some thm := cfg.use? then
    let pf := mkAppN (← mkConstWithFreshMVarLevels thm) #[xsE, hxsM]
    let want ← if upper then mkAppM ``LE.le #[mkApp2 (mkConst ``IExpr.denote) xsE eE, ← mkAppM ``Rat.cast #[cE]]
      else mkAppM ``LE.le #[← mkAppM ``Rat.cast #[cE], mkApp2 (mkConst ``IExpr.denote) xsE eE]
    unless ← isDefEq (← inferType pf) want do
      throwError "interval_grid: {thm} does not state this bound; it states{indentExpr (← inferType pf)}\n\
        expected{indentExpr want}"
    setGoals [hxsM.mvarId!]; inBoxesTac; setGoals saved
    return ← closeWith false pf
  -- (export := file): the problem file (and the problem as Lean source) for the CLI workflow
  if let some p := cfg.export? then
    let some prob := prob? | throwError "interval_grid: this expression has operations the tool \
      does not implement (only + - * / neg sqrt and natural powers)"
    let path ← relPath p
    IO.FS.writeFile path prob
    let src ← match iexprSrc e with
      | .ok s => pure s | .error m => throwError "interval_grid: {m}"
    let bsSrc := ", ".intercalate (bs.toList.map fun (a, b) => s!"({ratSrc a}, {ratSrc b})")
    let lean := s!"-- problem written by interval_grid (export := ...); fnv {hexU64 (fnv prob)}\n\
      e : {src}\nbs : [{bsSrc}]\nc : {ratSrc c}\nupper : {upper}\n"
    IO.FS.writeFile (path.toString ++ ".lean.txt") lean
    throwError "interval_grid: wrote {path} and {path}.lean.txt (fnv {hexU64 (fnv prob)}); \
      run `realfp-grid prove {path} -o CERT`, then use (cert := \"CERT\")"
  -- (explore := true)
  if cfg.explore then
    let t0 ← IO.monoMsNow
    let tool? ← if cfg.tool == `none || prob?.isNone then pure none else findTool
    match tool?, prob? with
    | some tool, some prob =>
      let pp := System.FilePath.mk s!"/tmp/realfp-grid-{hexU64 (fnv prob)}.problem"
      IO.FS.writeFile pp prob
      let eng := if cfg.tool == `auto then "auto" else cfg.tool.toString
      let (code, out) ← runTool tool (#["minmax", pp.toString, "--engine", eng] ++
        (if upper then #["--max"] else #[]) ++ #["--depth", toString depth])
      throwError "interval_grid (explore := true), realfp-grid ({(← IO.monoMsNow) - t0} ms, exit {code}):\n{out}\
        bound to prove: {fmtRat c} ({if upper then "upper" else "lower"}); variables {vars}"
    | _, _ =>
      let r := bnbMin e upper envK (if cfg.maxBoxes == 0 then 200000 else cfg.maxBoxes) 1e-9
      let (lo, hi) := if upper then (-r.upper, -r.lower) else (r.lower, r.upper)
      throwError "interval_grid (explore := true), built-in branch and bound ({(← IO.monoMsNow) - t0} ms, \
        {r.boxes} boxes): {if upper then "max" else "min"} f ∈ [{fmtFloat lo}, {fmtFloat hi}]; \
        bound to prove: {fmtRat c}; variables {vars}"
  -- the certificate
  let eStr ← ppExpr eE
  let key := match prob? with
    | some p => hexU64 (fnv p)
    | none => hexU64 (fnv s!"{bs.toList} {c} {upper} {eStr}")
  let mut hex? : Option String := none
  let mut how := ""
  let certPath? ← cfg.cert.mapM (fun p => (relPath p : MetaM _))
  if let some cp := certPath? then
    if ← cp.pathExists then
      let (k, line) ← readCert cp
      if k == some key && !line.isEmpty then hex? := some line; how := s!"cache {cp}"
      else logInfo m!"interval_grid: {cp} was made for another problem (fnv {k}, now {key}); searching again"
  let t0 ← IO.monoMsNow
  if hex?.isNone && cfg.tool != `none then
    if let some prob := prob? then
      if let some tool ← findTool then
        let pp := System.FilePath.mk s!"/tmp/realfp-grid-{key}.problem"
        let cp := System.FilePath.mk s!"/tmp/realfp-grid-{key}.cert"
        IO.FS.writeFile pp prob
        let eng := if cfg.tool == `auto then "auto" else cfg.tool.toString
        let mb := if cfg.maxBoxes == 0 then 1000000000 else cfg.maxBoxes
        let (code, out) ← runTool tool #["prove", pp.toString, "-o", cp.toString, "--engine", eng,
          "--depth", toString depth, "--max-boxes", toString mb]
        if code != 0 then
          throwError "interval_grid: realfp-grid found no certificate:\n{out}"
        let (_, line) ← readCert cp
        hex? := some line; how := s!"realfp-grid: {out.trimAscii}"
      else if cfg.tool != `auto then
        throwError "interval_grid: (tool := {cfg.tool}) but realfp-grid was not found (set \
          REALFP_GRID, put it on PATH, or build grid/ with grid/build.sh)"
  if hex?.isNone then
    let mb := if cfg.maxBoxes == 0 then 10000000 else cfg.maxBoxes
    match searchGrid fe upper cb d env depth mb with
    | .ok (h, n) => hex? := some h; how := s!"built-in search: {n} boxes"
    | .error n =>
      throwError "interval_grid: no certificate within depth {depth} / {mb} boxes ({n} evaluated, \
        built-in search). Try (explore := true) to see how close the bound is."
  let some hex := hex? | throwError "interval_grid: internal (no certificate)"
  let t1 ← IO.monoMsNow
  if let some cp := certPath? then
    if !how.startsWith "cache" then
      IO.FS.writeFile cp s!"# realfp-grid certificate v1\n# problem fnv {key}\n# {how}\n{hex}\n"
  -- the proof: one native_decide (the C checker)
  RealFP.requireNative
  withCurrHeartbeats do
  let lem := mkAppN (mkConst (if upper then ``RealFP.Grid.prove_le else ``RealFP.Grid.prove_ge))
    #[eE, bsE, cE, toExpr d, mkStrLit hex]
  let .forallE _ hT _ _ ← whnfR (← inferType lem) | throwError "interval_grid: internal (lemma)"
  let hM ← mkFreshExprMVar hT
  setGoals [hM.mvarId!]
  evalTactic (← `(tactic| native_decide))
  let t2 ← IO.monoMsNow
  setGoals [hxsM.mvarId!]; inBoxesTac; setGoals saved
  trace[interval] "interval_grid: {d} variable(s), certificate {hex.length * 4} bits ({how}, \
    {t1 - t0} ms), check {t2 - t1} ms"
  closeWith false (mkAppN lem #[← instantiateMVars hM, xsE, hxsM])

partial def gridCore (cfg : GCfg) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
  let t ← whnfR (← instantiateMVars (← goal.getType))
  match t.getAppFnArgs with
  | (``And, #[_, _]) =>
    let gs ← goal.apply (mkConst ``And.intro [])
    for g in gs do
      setGoals [g]; gridCore cfg
    setGoals []
  | (``LE.le, #[ty, _, a, b]) =>
    unless ← isDefEq ty (mkConst ``Real) do throwError "interval_grid: goal is not over ℝ"
    proveLe cfg a b
  | (``LT.lt, _) => throwError "interval_grid: strict inequalities are not supported; prove a \
      slightly tighter `≤` (e.g. with interval_grid) and conclude with `lt_of_le_of_lt`"
  | _ => throwError "interval_grid: unsupported goal {t}; expected `f ≤ g` or `f ≥ g` over ℝ \
      (variables bounded in context), or a conjunction of these"

/-- Introduce the variables, normalise the hypotheses, prove. -/
def runGrid (cfg : GCfg) : TacticM Unit := do
  liftMetaTactic fun g => do
    let (_, g) ← g.introNP (getIntrosSize (← instantiateMVars (← g.getType)))
    return [g]
  evalTactic (← `(tactic| try simp only [Set.mem_Icc, Set.mem_Ioo, Set.mem_Ico, Set.mem_Ioc,
    ge_iff_le, gt_iff_lt] at *))
  evalTactic (← `(tactic| try casesm* _ ∧ _))
  gridCore cfg

/-- `interval_grid` (options in any order): `(cert := "file")`, `(tool := auto|none|cpu|gpu|gpu32|gpu64)`,
`(depth := n)`, `(maxBoxes := n)`, `(explore := true)`, `(export := "file")`, `(use := thm)`.
See the module docstring and `docs/GPU.md`. -/
syntax (name := intervalGridTac) "interval_grid" (ppSpace gridOpt)* : tactic

def parseOpts (opts : Array Syntax) : CoreM GCfg := do
  let mut cfg : GCfg := {}
  for o in opts do
    let k := o[1].getId
    let v := o[3]
    if k == `depth then cfg := { cfg with depth := v.isNatLit?.getD 0 }
    else if k == `maxBoxes then cfg := { cfg with maxBoxes := v.isNatLit?.getD 0 }
    else if k == `tool then
      let t := v.getId
      unless [`auto, `none, `cpu, `gpu, `gpu32, `gpu64].contains t do
        throwErrorAt o "interval_grid: (tool := auto | none | cpu | gpu | gpu32 | gpu64)"
      cfg := { cfg with tool := t }
    else if k == `cert then
      let some s := v.isStrLit? | throwErrorAt o "interval_grid: (cert := \"file\")"
      cfg := { cfg with cert := some s }
    else if k == `export then
      let some s := v.isStrLit? | throwErrorAt o "interval_grid: (export := \"file\")"
      cfg := { cfg with export? := some s }
    else if k == `explore then cfg := { cfg with explore := v.getId != `false }
    else if k == `use then cfg := { cfg with use? := some (← realizeGlobalConstNoOverloadWithInfo v) }
    else throwErrorAt o "interval_grid: unknown option {k} (expected cert, tool, depth, maxBoxes, \
      explore, export, use)"
  return cfg

@[tactic intervalGridTac] def evalIntervalGrid : Tactic := fun stx => do
  runGrid (← parseOpts stx[1].getArgs)

/-- `#grid_export "file.problem" : statement` writes the problem file for `realfp-grid` and its
Lean source (`file.problem.lean.txt`, for `grid/gen_lean.py`), without proving anything. -/
syntax (name := gridExportCmd) "#grid_export " str " : " term : command

open Command in
@[command_elab gridExportCmd] def elabGridExport : CommandElab := fun stx => liftTermElabM do
  let some p := stx[1].isStrLit? | throwError "#grid_export: expected a file name"
  let ty ← Term.elabType stx[3]
  Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars ty
  let g ← mkFreshExprMVar ty
  try
    discard <| Tactic.run g.mvarId! (runGrid { export? := some p })
  catch ex =>
    let msg ← ex.toMessageData.toString
    if msg.startsWith "interval_grid: wrote" then logInfo m!"{msg}" else throw ex

end RealFP.Grid.Tac
