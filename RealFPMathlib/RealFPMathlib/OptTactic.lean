/-
Global optimisation goals for `realfp`: bounds on minima and maxima over boxes, found by branch
and bound and proved by kernel-checked certificates.

Supported statements (all over closed boxes with numeral bounds; `f` any `interval` expression):

* `∀ x ∈ S, c ≤ f x` / `f x ≤ c` (also `<`): handled by `interval` (bisection, derivative and
  multivariate centred-form certificates); a failure reports the approximate extremum.
* `∃ x ∈ S, f x ≤ c` (any number of real variables, `∃ x ∈ I, ∃ y ∈ J, …`, `∃ p : ℝ × ℝ, …`,
  any inequalities): a rational witness found by branch and bound, checked by `interval`.
* `∃ m : ℚ, ∀ x ∈ S, m ≤ f x` (or `f x ≥ m`, maxima with `≤ M`, `m : ℝ`): discovery; `m` is a
  short rational just below the branch-and-bound lower bound.
* `m ≤ sInf (f '' S)`, `sInf (f '' S) ≤ M`, `sSup` likewise, `sInf (f '' S) ∈ Set.Icc m M`,
  `|sInf (f '' S) - v| ≤ ε` (`S` a box `Set.Icc a b` or a product `Set.Icc a b ×ˢ …`): the
  idiomatic statement that the minimum lies in `[m, M]`, reduced by `RealFP.Opt.le_sInf_image_of`
  etc. to a universal bound (certificate) and a witness.
* `∃ x ∈ S, ∀ y ∈ S, f x ≤ f y` (argmin/argmax existence): compactness + `fun_prop` continuity.
* `∃ x ∈ Set.Icc a' b', ∀ y ∈ Set.Icc a b, f x ≤ f y` with `[a', b'] ⊆ [a, b]`: the minimiser
  lies in `[a', b']` (one variable; `RealFP.Opt.exists_isMin_in_Icc`).

`#realfp_min (x ∈ Set.Icc a b) (y ∈ Set.Icc c d), f` and `#realfp_max` print the approximate
extremum, a minimiser and statements that `realfp` proves.
-/
import RealFPMathlib.IntervalTactic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open Lean Meta Elab Tactic Term Command
open Interval64.KF RealFP RealFP.IntervalTactic

namespace RealFP.Opt

/-! ### Bridging lemmas (Mathlib statements of minima and maxima) -/

theorem le_sInf_image_of {α : Type*} {f : α → ℝ} {S : Set α} {m : ℝ} (hne : ∃ x, x ∈ S)
    (h : ∀ x ∈ S, m ≤ f x) : m ≤ sInf (f '' S) := by
  obtain ⟨x, hx⟩ := hne
  exact le_csInf ⟨f x, Set.mem_image_of_mem f hx⟩ (by rintro _ ⟨y, hy, rfl⟩; exact h y hy)

theorem sInf_image_le_of {α : Type*} {f : α → ℝ} {S : Set α} {M : ℝ}
    (hb : ∃ L : ℝ, ∀ x ∈ S, L ≤ f x) (h : ∃ x ∈ S, f x ≤ M) : sInf (f '' S) ≤ M := by
  obtain ⟨L, hL⟩ := hb
  obtain ⟨x, hx, hfx⟩ := h
  exact (csInf_le ⟨L, by rintro _ ⟨y, hy, rfl⟩; exact hL y hy⟩ (Set.mem_image_of_mem f hx)).trans hfx

theorem sSup_image_le_of {α : Type*} {f : α → ℝ} {S : Set α} {M : ℝ} (hne : ∃ x, x ∈ S)
    (h : ∀ x ∈ S, f x ≤ M) : sSup (f '' S) ≤ M := by
  obtain ⟨x, hx⟩ := hne
  exact csSup_le ⟨f x, Set.mem_image_of_mem f hx⟩ (by rintro _ ⟨y, hy, rfl⟩; exact h y hy)

theorem le_sSup_image_of {α : Type*} {f : α → ℝ} {S : Set α} {m : ℝ}
    (hb : ∃ U : ℝ, ∀ x ∈ S, f x ≤ U) (h : ∃ x ∈ S, m ≤ f x) : m ≤ sSup (f '' S) := by
  obtain ⟨U, hU⟩ := hb
  obtain ⟨x, hx, hfx⟩ := h
  exact hfx.trans (le_csSup ⟨U, by rintro _ ⟨y, hy, rfl⟩; exact hU y hy⟩ (Set.mem_image_of_mem f hx))

theorem abs_sub_le_of_le_le {s v ε : ℝ} (h1 : v - ε ≤ s) (h2 : s ≤ v + ε) : |s - v| ≤ ε :=
  abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-- A continuous function on a nonempty compact set attains its minimum. -/
theorem exists_isMin_of {α : Type*} [TopologicalSpace α] {S : Set α} (f : α → ℝ)
    (hS : IsCompact S) (hne : S.Nonempty) (hf : ContinuousOn f S) :
    ∃ x, x ∈ S ∧ ∀ y, y ∈ S → f x ≤ f y :=
  let ⟨x, hx, h⟩ := hS.exists_isMinOn hne hf
  ⟨x, hx, fun _ hy => h hy⟩

theorem exists_isMax_of {α : Type*} [TopologicalSpace α] {S : Set α} (f : α → ℝ)
    (hS : IsCompact S) (hne : S.Nonempty) (hf : ContinuousOn f S) :
    ∃ x, x ∈ S ∧ ∀ y, y ∈ S → f y ≤ f x :=
  let ⟨x, hx, h⟩ := hS.exists_isMaxOn hne hf
  ⟨x, hx, fun _ hy => h hy⟩

/-- Localisation of a minimiser: if `f q ≤ M` at some `q ∈ [a', b']` and `f > M` on the rest of
`[a, b]` (the closed pieces `[a, a']`, `[b', b]`), every minimiser on `[a, b]` lies in `[a', b']`. -/
theorem exists_isMin_in_Icc (f : ℝ → ℝ) {a b a' b' q M : ℝ} (hf : ContinuousOn f (Set.Icc a b))
    (ha : a ≤ a') (hb : b' ≤ b) (hq : q ∈ Set.Icc a' b') (hfq : f q ≤ M)
    (hl : ∀ y ∈ Set.Icc a a', M < f y) (hr : ∀ y ∈ Set.Icc b' b, M < f y) :
    ∃ x, x ∈ Set.Icc a' b' ∧ ∀ y, y ∈ Set.Icc a b → f x ≤ f y := by
  have hqS : q ∈ Set.Icc a b := ⟨ha.trans hq.1, hq.2.trans hb⟩
  obtain ⟨x, hx, hmin⟩ := exists_isMin_of f isCompact_Icc ⟨q, hqS⟩ hf
  refine ⟨x, ⟨?_, ?_⟩, hmin⟩
  · by_contra h
    have := hl x ⟨hx.1, (not_le.1 h).le⟩
    linarith [hmin q hqS]
  · by_contra h
    have := hr x ⟨(not_le.1 h).le, hx.2⟩
    linarith [hmin q hqS]

theorem exists_isMax_in_Icc (f : ℝ → ℝ) {a b a' b' q M : ℝ} (hf : ContinuousOn f (Set.Icc a b))
    (ha : a ≤ a') (hb : b' ≤ b) (hq : q ∈ Set.Icc a' b') (hfq : M ≤ f q)
    (hl : ∀ y ∈ Set.Icc a a', f y < M) (hr : ∀ y ∈ Set.Icc b' b, f y < M) :
    ∃ x, x ∈ Set.Icc a' b' ∧ ∀ y, y ∈ Set.Icc a b → f y ≤ f x := by
  have hqS : q ∈ Set.Icc a b := ⟨ha.trans hq.1, hq.2.trans hb⟩
  obtain ⟨x, hx, hmax⟩ := exists_isMax_of f isCompact_Icc ⟨q, hqS⟩ hf
  refine ⟨x, ⟨?_, ?_⟩, hmax⟩
  · by_contra h
    have := hl x ⟨hx.1, (not_le.1 h).le⟩
    linarith [hmax q hqS]
  · by_contra h
    have := hr x ⟨(not_le.1 h).le, hx.2⟩
    linarith [hmax q hqS]

/-! ### Numbers -/

set_option linter.concreteInstances false
variable [ExtTbl]

/-- A short decimal `≤ x` (`down`) or `≥ x`, within `slack` of `x`. -/
def niceRat (x : Float) (slack : Float) (down : Bool) : Option ℚ := do
  let q ← floatRat? x
  let s ← floatRat? slack
  for k in [0:18] do
    let p : ℚ := (10 ^ k : ℚ)
    let c : ℚ := if down then ((q * p).floor : ℚ) / p else ((q * p).ceil : ℚ) / p
    if (if down then q - c else c - q) ≤ s then return c
  return q

/-- Round `x` to the closest short decimal (`k` digits after the point), clamped to `[lo, hi]`. -/
def roundQ (x : Float) (k : Nat) (lo hi : ℚ) : ℚ :=
  match floatRat? x with
  | none => (lo + hi) / 2
  | some q =>
    let p : ℚ := (10 ^ k : ℚ)
    let c : ℚ := ((q * p + 1/2).floor : ℚ) / p
    max lo (min hi c)

/-- Syntax for a rational numeral of type `ℝ` (or `ℚ` if `rat`). -/
def qStx (q : ℚ) (rat : Bool := false) : TermElabM Term := do
  let n := Syntax.mkNumLit (toString q.num.natAbs)
  let d := Syntax.mkNumLit (toString q.den)
  let base ← if q.den == 1 then `(($n : ℝ)) else `((($n : ℝ) / $d))
  let baseQ ← if q.den == 1 then `(($n : ℚ)) else `((($n : ℚ) / $d))
  let t := if rat then baseQ else base
  if q.num < 0 then `(-$t) else pure t

/-! ### Boxes from hypotheses / binders -/

/-- Bounds `(lo, hi)` set by a constraint on variable `vars[i]`; `none` if it is not a bound. -/
def boundOf (vars : Array Expr) (t : Expr) : MetaM (Option (Nat × Option ℚ × Option ℚ)) := do
  let t ← instantiateMVars t
  let idx (x : Expr) : MetaM (Option Nat) := do
    for i in [0:vars.size] do
      if ← withReducible (isDefEq x vars[i]!) then return some i
    return none
  match t.getAppFnArgs with
  | (``Membership.mem, #[_, _, _, s, x]) =>
    let some i ← idx x | return none
    match (← whnfR s).getAppFnArgs with
    | (``Set.Icc, #[_, _, l, u]) =>
      let some ql ← ratOf? l | return none
      let some qu ← ratOf? u | return none
      return some (i, some ql, some qu)
    | _ => return none
  | (``LE.le, #[ty, _, l, r]) | (``LT.lt, #[ty, _, l, r]) =>
    unless (← whnfR ty).isConstOf ``Real do return none
    if let some i ← idx r then
      if let some q ← ratOf? l then return some (i, some q, none)
    if let some i ← idx l then
      if let some q ← ratOf? r then return some (i, none, some q)
    return none
  | (``GE.ge, #[ty, _, l, r]) | (``GT.gt, #[ty, _, l, r]) =>
    unless (← whnfR ty).isConstOf ``Real do return none
    if let some i ← idx l then
      if let some q ← ratOf? r then return some (i, some q, none)
    if let some i ← idx r then
      if let some q ← ratOf? l then return some (i, none, some q)
    return none
  | _ => return none

/-- Split conjunctions. -/
partial def conjuncts (t : Expr) : MetaM (List Expr) := do
  let t ← instantiateMVars t
  match t.getAppFnArgs with
  | (``And, #[a, b]) => return (← conjuncts a) ++ (← conjuncts b)
  | _ => return [t]

/-! ### Objective atoms -/

/-- An inequality `f ≤ c` (`upper`) or `c ≤ f` with `c` rational, `strict` for `<`. -/
structure Atom where
  f : IExpr
  c : ℚ
  upper : Bool
  strict : Bool
  deriving Inhabited

def Atom.goalFn (a : Atom) : KI → Bool :=
  let cK := KI.ofRat a.c
  match a.strict, a.upper with
  | false, true => gLe cK.lo | true, true => gLt cK.lo
  | false, false => gGe cK.hi | true, false => gGt cK.hi

/-- Parse an inequality between `interval` expressions in `vars`. -/
def atomOf? (vars : Array Expr) (t : Expr) : MetaM (Option Atom) := do
  let t ← instantiateMVars t
  let (l, r, strict) ← match t.getAppFnArgs with
    | (``LE.le, #[ty, _, l, r]) =>
      unless (← whnfR ty).isConstOf ``Real do return none
      pure (l, r, false)
    | (``LT.lt, #[ty, _, l, r]) =>
      unless (← whnfR ty).isConstOf ``Real do return none
      pure (l, r, true)
    | (``GE.ge, #[ty, _, l, r]) =>
      unless (← whnfR ty).isConstOf ``Real do return none
      pure (r, l, false)
    | (``GT.gt, #[ty, _, l, r]) =>
      unless (← whnfR ty).isConstOf ``Real do return none
      pure (r, l, true)
    | _ => return none
  if let some c ← ratOf? r then
    return some ⟨← reify vars l, c, true, strict⟩
  if let some c ← ratOf? l then
    return some ⟨← reify vars r, c, false, strict⟩
  let d ← mkAppM ``HSub.hSub #[l, r]
  return some ⟨← reify vars d, 0, true, strict⟩

/-- Does the atom hold at the rational point `q` (with the evaluator `interval` uses)? -/
def atomHoldsAt (a : Atom) (q : List ℚ) : Bool :=
  a.goalFn (evalF (q.map KI.ofRat) a.f)

/-- Signed objective for the search: minimise `f` for `f ≤ c`, maximise for `c ≤ f`. -/
def atomMin (a : Atom) (env : List KI) : BBResult := bnbMin a.f (!a.upper) env 4000 1e-12

/-- The atom's goal predicate on a 128-bit enclosure. -/
def Atom.goalQ (a : Atom) : Interval128.Dy.DI → Bool :=
  match a.strict, a.upper with
  | false, true => Interval128.Dy.gLe a.c | true, true => Interval128.Dy.gLt a.c
  | false, false => Interval128.Dy.gGe a.c | true, false => Interval128.Dy.gGt a.c

/-- Does the atom hold at `q` with the 128-bit evaluator? -/
def atomHoldsAtQ (a : Atom) (q : List ℚ) : Bool :=
  a.goalQ (Interval128.Dy.evalQ (q.map fun r => Interval128.Dy.DI.ofRatI r r) a.f)

/-- One variable at precision 128: a stationary point of the atom's left side near `x₀`, by
bisection on the sign of the derivative at dyadic points (110 steps from a bracket around `x₀`
inside `[l, h]`). -/
def refineStatQ (f : IExpr) (l h : ℚ) (x0 : Float) : Option ℚ := Id.run do
  let d := f.deriv 0
  let sgn (q : ℚ) : Option Bool :=   -- `some true`: f' > 0
    let F := Interval128.Dy.evalQ [Interval128.Dy.DI.ofRatI q q] d
    if Interval128.Dy.gGt 0 F then some true else if Interval128.Dy.gLt 0 F then some false
    else none
  let x0q := (floatRat? x0).getD ((l + h) / 2)
  -- bracket: widen around x0 until the derivative signs differ
  let mut r : ℚ := (h - l) / 2 ^ 20
  let mut br : Option (ℚ × ℚ) := none
  for _ in [0:21] do
    let lo := max l (x0q - r)
    let hi := min h (x0q + r)
    match sgn lo, sgn hi with
    | some sl, some sh => if sl != sh then br := some (lo, hi); break
    | _, _ => pure ()
    r := r * 2
  let some (lo0, hi0) := br | return none
  let up := (sgn hi0).getD true
  let mut lo := lo0
  let mut hi := hi0
  for _ in [0:110] do
    let m := Interval128.Dy.toRat (Interval128.Dy.ofRatDn ((lo + hi) / 2))
    match sgn m with
    | some b => if b == up then hi := m else lo := m
    | none => return some m
  return some lo

def refineQ (a : Atom) (l h : ℚ) (x0 : Float) : Option ℚ := refineStatQ a.f l h x0

/-! ### 128-bit helpers (localisation and `#realfp_min (precision := 128)`) -/

def isPrec128 (opts : Array (TSyntax `intervalOpt)) : Bool :=
  opts.any fun o => o.raw[1].getId == `precision && o.raw[3].isNatLit? == some 128

/-- Rigorous upper end of the 128-bit enclosure of `±f` at the point `q` (`-f` for `max`). -/
def valQ (f : IExpr) (isMin : Bool) (q : List ℚ) : Option ℚ :=
  let F := Interval128.Dy.evalQ (q.map fun r => Interval128.Dy.DI.ofRatI r r) f
  if isMin then F.hi.map Interval128.Dy.toRat else F.lo.map fun d => -Interval128.Dy.toRat d

/-- Midpoint of the 128-bit enclosure of `±f` at `q`. -/
def midValQ (f : IExpr) (isMin : Bool) (q : List ℚ) : Option ℚ :=
  let F := Interval128.Dy.evalQ (q.map fun r => Interval128.Dy.DI.ofRatI r r) f
  match F.lo, F.hi with
  | some a, some b =>
    let m := (Interval128.Dy.toRat a + Interval128.Dy.toRat b) / 2
    some (if isMin then m else -m)
  | _, _ => none

/-- The shortest decimal in `[lo, hi]` (`lo` if none with at most 60 digits). -/
def shortIn (lo hi : ℚ) : ℚ := Id.run do
  for k in [0:61] do
    let p : ℚ := 10 ^ k
    let c : ℚ := ((lo * p).ceil : ℚ) / p
    if c ≤ hi then return c
  return lo

/-- Decimal string of `q` with `d` digits after the point (rounded toward `-∞`). -/
def fmtDec (q : ℚ) (d : Nat := 36) : String :=
  let p : ℚ := 10 ^ d
  let n : ℤ := (q * p).floor
  let s := toString n.natAbs
  let s := if s.length ≤ d then String.ofList (List.replicate (d + 1 - s.length) '0') ++ s else s
  let ip := String.ofList (s.toList.take (s.length - d))
  let fp := ((s.toList.drop (s.length - d)).reverse.dropWhile (· == '0')).reverse
  (if n < 0 then "-" else "") ++ ip ++ (if fp.isEmpty then "" else "." ++ String.ofList fp)

/-- Short decimal for display (significant digits `d`). -/
def fmtSig (q : ℚ) (d : Nat := 36) : String := Id.run do
  if q == 0 then return "0"
  let a := |q|
  let mut k : Nat := 0
  -- digits after the point so that about `d` significant digits show
  let mut t := a
  while t < 1 && k < 400 do
    t := t * 10; k := k + 1
  let mut ip : Nat := 0
  let mut u := a
  while u ≥ 10 do
    u := u / 10; ip := ip + 1
  fmtDec q (if k > 0 then k + d - 1 else d - min d (ip + 1))

/-- Centred-form lower bound of `g` on the box `env` (128 bits), and the natural one. -/
def lowerQ (g : IExpr) (dg : List IExpr) (env : List Interval128.Dy.DI) : Option ℚ := do
  let nat := (Interval128.Dy.evalQ env g).lo.map Interval128.Dy.toRat
  let ms ← env.mapM fun X => do
    let a ← X.lo; let b ← X.hi; pure (Interval128.Dy.centre a b)
  let pts := ms.map Interval128.Dy.DI.pt
  let fm := Interval128.Dy.evalQ pts g
  let terms := (List.range env.length).map fun j =>
    let X := env.getD j Interval128.Dy.DI.zero
    let m := Interval128.Dy.DI.pt (ms.getD j Interval128.Dy.zero)
    Interval128.Dy.DI.mul (Interval128.Dy.evalQ env (dg.getD j (.rat 0))) (Interval128.Dy.DI.sub X m)
  let cen := (terms.foldl Interval128.Dy.DI.add fm).lo.map Interval128.Dy.toRat
  match nat, cen with
  | some a, some b => pure (max a b)
  | some a, none => pure a
  | none, some b => pure b
  | none, none => none

structure QNode where
  env : List Interval128.Dy.DI
  lb : ℚ
  deriving Inhabited

/-- Branch and bound with 128-bit enclosures (natural and centred forms): minimum of `g` on the
box. Returns `(lower, upper, argmin, boxes)`; nothing is proved. -/
def bnbMinQ (g : IExpr) (bs : List (ℚ × ℚ)) (maxBoxes : Nat := 20000) (relTol : ℚ := 1 / 10 ^ 32) :
    ℚ × ℚ × List ℚ × Nat := Id.run do
  let n := bs.length
  let dg := (List.range n).map g.deriv
  let env0 := Interval128.Dy.boxes bs
  let centreOf (env : List Interval128.Dy.DI) : List ℚ := env.map fun X =>
    match X.lo, X.hi with
    | some a, some b => Interval128.Dy.toRat (Interval128.Dy.centre a b)
    | _, _ => 0
  let upAt (q : List ℚ) : Option ℚ :=
    (Interval128.Dy.evalQ (q.map fun r => Interval128.Dy.DI.ofRatI r r) g).hi.map Interval128.Dy.toRat
  let c0 := centreOf env0
  let mut best : ℚ := (upAt c0).getD (10 ^ 300)
  let mut arg := c0
  let mut work : Array QNode := #[⟨env0, (lowerQ g dg env0).getD (-(10 ^ 300))⟩]
  let mut count := 0
  let mut lower : ℚ := work[0]!.lb
  while !work.isEmpty do
    -- the node with the smallest lower bound
    let mut bi := 0
    for i in [1:work.size] do
      if work[i]!.lb < work[bi]!.lb then bi := i
    let nd := work[bi]!
    lower := nd.lb
    if best - nd.lb ≤ relTol * max 1 |best| || count ≥ maxBoxes then break
    work := work.eraseIdxIfInBounds bi
    -- split the widest coordinate at its centre
    let mut wi := 0
    let mut ww : ℚ := -1
    for j in [0:n] do
      let X := nd.env.getD j Interval128.Dy.DI.zero
      if let (some a, some b) := (X.lo, X.hi) then
        let w := Interval128.Dy.toRat b - Interval128.Dy.toRat a
        if w > ww then ww := w; wi := j
    let X := nd.env.getD wi Interval128.Dy.DI.zero
    let some a := X.lo | break
    let some b := X.hi | break
    let d := Interval128.Dy.centre a b
    for Y in [Interval128.Dy.leftAt X d, Interval128.Dy.rightAt X d] do
      count := count + 1
      let env := nd.env.set wi Y
      let c := centreOf env
      if let some u := upAt c then
        if u < best then best := u; arg := c
      let lb := (lowerQ g dg env).getD (-(10 ^ 300))
      if lb < best then work := work.push ⟨env, lb⟩
  if work.isEmpty then lower := best
  return (min lower best, best, arg, count)

/-! ### Witnesses for `∃ x ∈ S, …` -/

/-- Find a short rational point in the box satisfying every atom. -/
def findWitness (atoms : Array Atom) (bs : List (ℚ × ℚ)) : Option (List ℚ) := Id.run do
  let env := boxes bs
  let mid := bs.map fun (l, h) => (l + h) / 2
  let mut cands : Array (List Float) := #[mid.map qToF]
  for a in atoms do
    cands := cands.push (atomMin a env).arg
  -- short grid points (exact minimisers are often simple numbers)
  let n := bs.length
  let grids := if n ≤ 2 then [2, 4, 8, 10, 16, 20] else if n == 3 then [2, 4, 10] else [2]
  let mut gridPts : Array (List ℚ) := #[]
  for g in grids do
    let axes := bs.map fun (l, h) => (List.range (g + 1)).map fun k => l + (h - l) * k / g
    let pts := axes.foldr (fun ax acc => ax.flatMap fun v => acc.map (v :: ·)) [[]]
    gridPts := gridPts ++ pts.toArray
  -- simple coordinate refinement of the first candidate list is unnecessary: the B&B point is
  -- within the final box of the search
  for p in cands do
    for k in [0:18] do
      let q := (p.zip bs).map fun (x, (l, h)) => roundQ x k l h
      if atoms.all (atomHoldsAt · q) then return some q
    -- exact float point
    let q? := (p.zip bs).mapM fun (x, (l, h)) => (floatRat? x).map fun r => max l (min h r)
    if let some q := q? then
      if atoms.all (atomHoldsAt · q) then return some q
  for q in gridPts do
    if atoms.all (atomHoldsAt · q) then return some q
  return none

/-- `findWitness` checked with the 128-bit evaluator (plus a 128-bit refinement of a stationary
point in one variable). -/
def findWitnessQ (atoms : Array Atom) (bs : List (ℚ × ℚ)) : Option (List ℚ) := Id.run do
  let env := boxes bs
  let mid := bs.map fun (l, h) => (l + h) / 2
  let mut cands : Array (List Float) := #[mid.map qToF]
  for a in atoms do
    cands := cands.push (atomMin a env).arg
  -- short grid points (exact minimisers are often simple numbers)
  let n := bs.length
  let grids := if n ≤ 2 then [2, 4, 8, 10, 16, 20] else if n == 3 then [2, 4, 10] else [2]
  let mut gridPts : Array (List ℚ) := #[]
  for g in grids do
    let axes := bs.map fun (l, h) => (List.range (g + 1)).map fun k => l + (h - l) * k / g
    let pts := axes.foldr (fun ax acc => ax.flatMap fun v => acc.map (v :: ·)) [[]]
    gridPts := gridPts ++ pts.toArray
  -- simple coordinate refinement of the first candidate list is unnecessary: the B&B point is
  -- within the final box of the search
  for p in cands do
    for k in [0:18] do
      let q := (p.zip bs).map fun (x, (l, h)) => roundQ x k l h
      if atoms.all (atomHoldsAtQ · q) then return some q
    -- exact float point
    let q? := (p.zip bs).mapM fun (x, (l, h)) => (floatRat? x).map fun r => max l (min h r)
    if let some q := q? then
      if atoms.all (atomHoldsAtQ · q) then return some q
  for q in gridPts do
    if atoms.all (atomHoldsAtQ · q) then return some q
  -- one variable: refine a stationary point of each atom at 128 bits
  if let [(l, h)] := bs then
    for a in atoms do
      if let some q := refineQ a l h ((atomMin a env).arg.headD 0) then
        if atoms.all (atomHoldsAtQ · [q]) then return some [q]
  return none

/-- Close a goal made of `∃ x : ℝ`, `∧` and atoms, using the witnesses `qs` in binder order. -/
partial def closeWith (qs : Array ℚ) (i : Nat) (prec128 : Bool := false) : TacticM Nat := do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  match t.getAppFnArgs with
  | (``Exists, #[ty, _]) =>
    unless (← whnfR ty).isConstOf ``Real do throwError "realfp: unsupported binder type {ty}"
    let some q := qs[i]? | throwError "realfp: internal (witness count)"
    let qt ← qStx q
    evalTactic (← `(tactic| refine ⟨$qt, ?_⟩))
    closeWith qs (i + 1) prec128
  | (``And, #[_, _]) =>
    evalTactic (← `(tactic| refine ⟨?_, ?_⟩))
    let gs ← getGoals
    let rest := gs.drop 2
    setGoals [gs[0]!]
    let i ← closeWith qs i prec128
    setGoals [gs[1]!]
    let i ← closeWith qs i prec128
    setGoals rest
    return i
  | _ =>
    if prec128 then
      evalTactic (← `(tactic| first
        | (norm_num; done)
        | (simp only [Set.mem_Icc]; constructor <;> norm_num; done)
        | interval (precision := 128)))
    else
      evalTactic (← `(tactic| first
        | (norm_num; done)
        | (simp only [Set.mem_Icc]; constructor <;> norm_num; done)
        | interval))
    return i

/-- Peel `∃ x : ℝ` binders and conjunctions; `k` gets the variables and the atoms. -/
partial def peel {α} (todo : List Expr) (vars : Array Expr) (atoms : Array Expr)
    (k : Array Expr → Array Expr → MetaM α) : MetaM α := do
  match todo with
  | [] => k vars atoms
  | t :: rest =>
    let t ← instantiateMVars t
    match t.getAppFnArgs with
    | (``Exists, #[ty, p]) =>
      unless (← whnfR ty).isConstOf ``Real do
        throwError "realfp: existential over {ty}; use real variables (`∃ x : ℝ`, or \
          `∃ p : ℝ × ℝ` which is split into coordinates)"
      let n := match p with | .lam n .. => n | _ => `x
      withLocalDeclD n ty fun x => peel (p.beta #[x] :: rest) (vars.push x) atoms k
    | (``And, #[a, b]) => peel (a :: b :: rest) vars atoms k
    | _ => peel rest vars (atoms.push t) k

/-- Prove `∃ x ∈ S, P x` (inequalities `P`) by a witness. -/
def proveWitnessCore (prec128 : Bool := false) : TacticM Unit := do
  evalTactic (← `(tactic| try simp only [Prod.exists, Set.mem_prod, and_assoc, exists_prop]))
  let goal ← getMainGoal
  let qs ← goal.withContext do
    let t ← instantiateMVars (← goal.getType)
    peel [t] #[] #[] fun vars props => do
      let n := vars.size
      let mut lo : Array (Option ℚ) := Array.replicate n none
      let mut hi : Array (Option ℚ) := Array.replicate n none
      let mut objs : Array Expr := #[]
      -- pass 1: boxes `x ∈ Set.Icc a b`
      for p in props do
        if p.isAppOf ``Membership.mem then
          if let some (i, l, h) ← boundOf vars p then
            if lo[i]!.isNone then lo := lo.set! i l
            if hi[i]!.isNone then hi := hi.set! i h
            continue
        objs := objs.push p
      -- pass 2: numeral bounds on single variables (if still missing)
      let mut atomsE : Array Expr := #[]
      for p in objs do
        if let some (i, l, h) ← boundOf vars p then
          if (l.isSome && lo[i]!.isNone) || (h.isSome && hi[i]!.isNone) then
            if l.isSome && lo[i]!.isNone then lo := lo.set! i l
            if h.isSome && hi[i]!.isNone then hi := hi.set! i h
            continue
        atomsE := atomsE.push p
      let mut bs : List (ℚ × ℚ) := []
      for i in [0:n] do
        match lo[i]!, hi[i]! with
        | some l, some h =>
          unless l ≤ h do throwError "realfp: empty box for {vars[i]!}: [{l}, {h}]"
          bs := bs ++ [(l, h)]
        | _, _ => throwError "realfp: {vars[i]!} needs a numeral lower and upper bound \
            (`{vars[i]!} ∈ Set.Icc a b`)"
      let mut atoms : Array Atom := #[]
      for p in atomsE do
        match ← atomOf? vars p with
        | some a => atoms := atoms.push a
        | none => throwError "realfp: unsupported condition {p} in an existential goal \
            (expected inequalities; equations go to `root_exists`)"
      let some q := (if prec128 then findWitnessQ atoms bs else findWitness atoms bs) |
        let msg := if h : 0 < atoms.size then
          let r := atomMin atoms[0] (boxes bs)
          let ext := if atoms[0].upper then r.upper else -r.upper
          s!" (branch and bound: the best value of the first condition's left side is ≈ \
            {fmtFloat ext} at {r.arg.map fmtFloat})"
          else ""
        throwError "realfp: no witness found{msg}; the condition may fail on the whole box or \
          be too tight"
      return q.toArray
  let _ ← closeWith qs 0 prec128
  pure ()

/-! ### Discovery: `∃ m, ∀ x ∈ S, m ≤ f x` -/

structure BoundGoal where
  f : IExpr
  bs : List (ℚ × ℚ)
  /-- `m ≤ f` (lower bound on `f`); else `f ≤ m`. -/
  lower : Bool
  strict : Bool


/-- `proveWitnessCore` with the registered functions of the goal. -/
def proveWitness (prec128 : Bool := false) : TacticM Unit :=
  withRegistered (proveWitnessCore prec128)

/-- Analyse `∀ x, x ∈ S → … → R m (f x)` with the bound variable `m`. -/
def analyseBound (m : Expr) (body : Expr) : MetaM BoundGoal := do
  forallTelescopeReducing body fun xs atom => do
    let mut vars : Array Expr := #[]
    for x in xs do
      if (← whnfR (← inferType x)).isConstOf ``Real then vars := vars.push x
    let n := vars.size
    let mut lo : Array (Option ℚ) := Array.replicate n none
    let mut hi : Array (Option ℚ) := Array.replicate n none
    for x in xs do
      let ty ← inferType x
      unless (← whnfR ty).isConstOf ``Real do
        for c in ← conjuncts ty do
          let some (i, l, h) ← boundOf vars c |
            throwError "realfp: unsupported hypothesis {c}; expected numeral bounds"
          if l.isSome then lo := lo.set! i l
          if h.isSome then hi := hi.set! i h
    let mut bs : List (ℚ × ℚ) := []
    for i in [0:n] do
      match lo[i]!, hi[i]! with
      | some l, some h => bs := bs ++ [(l, h)]
      | _, _ => throwError "realfp: {vars[i]!} needs a numeral lower and upper bound"
    let hasM (e : Expr) := e.containsFVar m.fvarId!
    let (l, r, strict) ← match atom.getAppFnArgs with
      | (``LE.le, #[_, _, l, r]) => pure (l, r, false)
      | (``LT.lt, #[_, _, l, r]) => pure (l, r, true)
      | (``GE.ge, #[_, _, l, r]) => pure (r, l, false)
      | (``GT.gt, #[_, _, l, r]) => pure (r, l, true)
      | _ => throwError "realfp: expected an inequality with the bound, got {atom}"
    if hasM l && !hasM r then
      return ⟨← reify vars r, bs, true, strict⟩
    if hasM r && !hasM l then
      return ⟨← reify vars l, bs, false, strict⟩
    throwError "realfp: the bound variable must be one side of {atom}"

/-- Prove `∃ m, ∀ x ∈ S, m ≤ f x` (or `f x ≤ m`) by branch and bound + `interval`. -/
def proveDiscoverCore (opts : Array (TSyntax `intervalOpt)) : TacticM Unit := do
  let goal ← getMainGoal
  let (bg, isRat) ← goal.withContext do
    let t ← instantiateMVars (← goal.getType)
    let (``Exists, #[ty, p]) := t.getAppFnArgs | throwError "realfp: internal (discover)"
    let isRat := (← whnfR ty).isConstOf ``Rat
    unless isRat || (← whnfR ty).isConstOf ``Real do
      throwError "realfp: the bound must be in ℚ or ℝ, got {ty}"
    withLocalDeclD `m ty fun m => do return (← analyseBound m (p.beta #[m]), isRat)
  let r := bnbMin bg.f (!bg.lower) (boxes bg.bs) 20000 1e-6
  let ext := if bg.lower then r.lower else -r.lower   -- bound on f from the enclosures
  let mut lastErr : MessageData := m!""
  for k in [2, 1, 0] do
    let slack : Float := (10 : Float) ^ (-(k.toFloat)) * (1 + ext.abs)
    let target := if bg.lower then ext - slack / 2 else ext + slack / 2
    let some c := niceRat target (slack / 2) bg.lower | throwError "realfp: internal (bound)"
    let s ← saveState
    try
      let ct ← qStx c isRat
      evalTactic (← `(tactic| refine ⟨$ct, ?_⟩))
      evalTactic (← `(tactic| interval $opts*))
      return
    catch ex =>
      lastErr := ex.toMessageData
      s.restore
  throwError "realfp: could not certify a bound near {fmtFloat ext}: {lastErr}"

/-! ### `sInf` / `sSup` goals -/


/-- `proveDiscoverCore` with the registered functions of the goal. -/
def proveDiscover (opts : Array (TSyntax `intervalOpt)) : TacticM Unit := withRegistered (proveDiscoverCore opts)

def isInfSup (e : Expr) : Option (Bool × Expr × Expr) :=  -- (isInf, f, S)
  match e.getAppFnArgs with
  | (``InfSet.sInf, #[_, _, img]) | (``SupSet.sSup, #[_, _, img]) =>
    match img.getAppFnArgs with
    | (``Set.image, #[_, _, f, S]) => some (e.isAppOf ``InfSet.sInf, f, S)
    | _ => none
  | _ => none

def mentionsInfSup (e : Expr) : Bool :=
  (e.find? fun s => s.isConstOf ``InfSet.sInf || s.isConstOf ``SupSet.sSup).isSome

/-- Reduce an `sInf`/`sSup` goal by one bridging lemma; returns the new goals. -/
def reduceInfSup : TacticM Unit := do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  let t' ← whnfR t
  match t.getAppFnArgs with
  | (``Membership.mem, #[_, _, _, _, _]) =>
    evalTactic (← `(tactic| refine Set.mem_Icc.2 ⟨?_, ?_⟩))
  | (``LE.le, #[_, _, l, r]) =>
    match isInfSup l, isInfSup r with
    | _, some (true, _, _) => evalTactic (← `(tactic| refine RealFP.Opt.le_sInf_image_of ?_ ?_))
    | some (true, _, _), _ => evalTactic (← `(tactic| refine RealFP.Opt.sInf_image_le_of ?_ ?_))
    | _, some (false, _, _) => evalTactic (← `(tactic| refine RealFP.Opt.le_sSup_image_of ?_ ?_))
    | some (false, _, _), _ => evalTactic (← `(tactic| refine RealFP.Opt.sSup_image_le_of ?_ ?_))
    | _, _ =>
      -- `|s - v| ≤ ε`
      match l.getAppFnArgs with
      | (``abs, #[_, _, _, _]) =>
        evalTactic (← `(tactic| refine RealFP.Opt.abs_sub_le_of_le_le ?_ ?_))
      | _ => throwError "realfp: unsupported sInf/sSup goal {t}"
  | (``GE.ge, _) => evalTactic (← `(tactic| show _ ≤ _))
  | (``Eq, #[_, _, _]) => evalTactic (← `(tactic| refine le_antisymm ?_ ?_))
  | _ =>
    let _ := t'
    throwError "realfp: unsupported sInf/sSup goal {t}; expected `m ≤ sInf (f '' S)`, \
      `sInf (f '' S) ≤ M`, `sInf (f '' S) ∈ Set.Icc m M`, `|sInf (f '' S) - v| ≤ ε` (or sSup)"
  -- tidy the new goals: beta-reduce `f x`, split products
  let gs ← getGoals
  let mut out := #[]
  for g in gs do
    setGoals [g]
    evalTactic (← `(tactic| try beta_reduce))
    evalTactic (← `(tactic| try simp only [Prod.forall, Prod.exists, Set.mem_prod, and_imp,
      and_assoc, exists_prop]))
    out := out ++ (← getGoals)
  setGoals out.toList

/-! ### Argmin / argmax existence -/

def firstTac : List (TSyntax `tactic) → TacticM Unit
  | [] => throwError "realfp: no tactic succeeded"
  | [t] => evalTactic t
  | t :: ts => do
    let s ← saveState
    try evalTactic t catch _ => s.restore; firstTac ts


/-- `∃ x, x ∈ S ∧ ∀ y, y ∈ S' → lhs ≤ rhs`: returns `(min?, f, S, S')`. -/
def argGoal? (t : Expr) : MetaM (Option (Bool × Expr × Expr × Expr)) := do
  let (``Exists, #[ty, p]) := t.getAppFnArgs | return none
  withLocalDeclD `x ty fun x => do
    let body ← instantiateMVars (p.beta #[x])
    let (``And, #[mem, rest]) := body.getAppFnArgs | return none
    let (``Membership.mem, #[_, _, _, S, x']) := mem.getAppFnArgs | return none
    unless x' == x do return none
    let .forallE yn yty b1 _ := rest | return none
    withLocalDeclD yn yty fun y => do
      let b1 := b1.instantiate1 y
      let .forallE _ memY b2 _ := b1 | return none
      let (``Membership.mem, #[_, _, _, S', y']) := memY.getAppFnArgs | return none
      unless y' == y do return none
      if b2.hasLooseBVars then return none
      let (l, r, isMin) ← match b2.getAppFnArgs with
        | (``LE.le, #[_, _, l, r]) => pure (l, r, true)
        | (``GE.ge, #[_, _, l, r]) => pure (r, l, true)
        | _ => return none
      -- min: f x ≤ f y  (l mentions x, r mentions y); max: f y ≤ f x
      let (fx, fy) := if l.containsFVar x.fvarId! then (l, r) else (r, l)
      let isMin := isMin == l.containsFVar x.fvarId!
      if fy.containsFVar x.fvarId! || fx.containsFVar y.fvarId! then return none
      let f ← mkLambdaFVars #[y] fy
      unless ← isDefEq (f.beta #[x]) fx do return none
      return some (isMin, f, S, S')

def proveArgCore (opts : Array (TSyntax `intervalOpt)) : TacticM Unit := do
  let goal ← getMainGoal
  let some (isMin, f, S, S') ← goal.withContext do argGoal? (← instantiateMVars (← goal.getType))
    | throwError "realfp: expected `∃ x ∈ S, ∀ y ∈ S, f x ≤ f y` (or `f y ≤ f x`)"
  let same ← goal.withContext do isDefEq S S'
  if same then
    let lem := if isMin then ``exists_isMin_of else ``exists_isMax_of
    let gs ← goal.withContext do
      let e ← mkAppOptM lem #[none, none, S, f]
      goal.apply e
    setGoals gs
    for g in gs do
      setGoals [g]
      let t ← instantiateMVars (← g.getType)
      if t.isAppOf ``IsCompact then
        evalTactic (← `(tactic| repeat' (first | exact isCompact_Icc | apply IsCompact.prod)))
      else if t.isAppOf ``Set.Nonempty then
        evalTactic (← `(tactic| repeat' (first | (apply Set.Nonempty.prod) | (apply Set.nonempty_Icc.2; norm_num))))
      else if t.isAppOf ``ContinuousOn then
        let t1 ← `(tactic| fun_prop)
        let t2 ← `(tactic| (apply Continuous.continuousOn; fun_prop))
        let t3 ← `(tactic| (apply Continuous.continuousOn; continuity))
        firstTac [t1, t2, t3]
      else if !(← g.isAssigned) then
        throwError "realfp: unexpected side goal {t}"
    return
  -- localisation `[a', b'] ⊆ [a, b]` (one variable)
  let some (a', b') ← goal.withContext do
      match (← whnfR S).getAppFnArgs with
      | (``Set.Icc, #[_, _, l, u]) => pure (some (l, u))
      | _ => pure none
    | throwError "realfp: localisation needs boxes `Set.Icc`"
  let some (a, b) ← goal.withContext do
      match (← whnfR S').getAppFnArgs with
      | (``Set.Icc, #[_, _, l, u]) => pure (some (l, u))
      | _ => pure none
    | throwError "realfp: localisation needs boxes `Set.Icc`"
  let (fI, qa, qb, qa', qb') ← goal.withContext do
    let some qa ← ratOf? a | throwError "realfp: {a} is not a numeral"
    let some qb ← ratOf? b | throwError "realfp: {b} is not a numeral"
    let some qa' ← ratOf? a' | throwError "realfp: {a'} is not a numeral"
    let some qb' ← ratOf? b' | throwError "realfp: {b'} is not a numeral"
    withLocalDeclD `y (mkConst ``Real) fun y => do
      let body ← instantiateMVars (f.beta #[y])
      return (← reify #[y] body, qa, qb, qa', qb')
  unless qa ≤ qa' && qb' ≤ qb do throwError "realfp: [{qa'}, {qb'}] is not inside [{qa}, {qb}]"
  -- witness q and level M: B&B on the inner box, M between f(q) and the outer minimum
  let inner := bnbMin fI (!isMin) (boxes [(qa', qb')]) 4000 1e-12
  let outer := [(qa, qa'), (qb', qb)].filter (fun (l, h) => l ≤ h)
  let outs := outer.map fun bx => bnbMin fI (!isMin) (boxes [bx]) 4000 1e-9
  let (q, M) ← if isPrec128 opts then do
      -- 128 bits: a stationary point by derivative bisection, values from `evalQ`
      let x0 := inner.arg.headD 0
      let clampQ (r : ℚ) : ℚ := max qa' (min qb' r)
      let qs := (refineStatQ fI qa' qb' x0).getD (clampQ ((floatRat? x0).getD ((qa' + qb') / 2)))
      let some fqs := valQ fI isMin [qs] |
        throwError "realfp: (precision := 128) no 128-bit value of f at {fmtRat qs}"
      let mut outPts : List ℚ := []
      for (l, h) in outer do outPts := outPts ++ [l, h]
      for r in outs do
        if let some v := floatRat? (r.arg.headD 0) then
          if outer.any (fun (l, h) => l ≤ v && v ≤ h) then outPts := outPts ++ [v]
      let outVals := outPts.filterMap fun p => midValQ fI isMin [p]
      let some outMin := outVals.min? |
        throwError "realfp: (precision := 128) no outer piece to compare with"
      unless fqs < outMin do
        throwError "realfp: (precision := 128) cannot localise: the best value in \
          [{fmtRat qa'}, {fmtRat qb'}] is ≈ {fmtSig (if isMin then fqs else -fqs) 20}, but outside \
          it ≈ {fmtSig (if isMin then outMin else -outMin) 20} (the gap must exceed the 128-bit \
          resolution)"
      let target := fqs + (outMin - fqs) / 4
      let mut q := qs
      for k in [0:60] do
        let p : ℚ := 10 ^ k
        let c := clampQ (((qs * p).floor : ℚ) / p)
        let c' := clampQ (((qs * p).ceil : ℚ) / p)
        if (valQ fI isMin [c]).any (· ≤ target) then q := c; break
        if (valQ fI isMin [c']).any (· ≤ target) then q := c'; break
      let fq := (valQ fI isMin [q]).getD fqs
      let Ms := shortIn (fq + (outMin - fq) / 3) (fq + 2 * (outMin - fq) / 3)
      pure (q, if isMin then Ms else -Ms)
    else do
      let outMin := outs.foldl (fun m r => min m r.lower) (1.0/0.0)   -- of ±f
      let valAt (q : ℚ) : Float :=
        let F := evalF [KI.ofRat q] fI
        if isMin then fixNaN (toFl F.hi) (1.0/0.0) else fixNaN (-(toFl F.lo)) (1.0/0.0)
      let target := inner.upper + (outMin - inner.upper) / 4
      let cands := (List.range 18).map fun k => roundQ (inner.arg.headD 0) k qa' qb'
      let q := (cands.find? fun q => valAt q ≤ target).getD (cands.getLast?.getD qa')
      let fqs := valAt q
      let fqv := if isMin then fqs else -fqs
      unless fqs < outMin do
        throwError "realfp: cannot localise: the best value in [{fmtRat qa'}, {fmtRat qb'}] is ≈ \
          {fmtFloat fqv}, but outside it ≈ {fmtFloat (if isMin then outMin else -outMin)}"
      let Ms := (fqs + outMin) / 2
      let Mv := if isMin then Ms else -Ms
      let some M := niceRat Mv ((outMin - fqs) / 4) (!isMin) | throwError "realfp: internal (level)"
      pure (q, M)
  let lem := if isMin then ``exists_isMin_in_Icc else ``exists_isMax_in_Icc
  let qT ← qStx q
  let MT ← qStx M
  let fT ← Term.exprToSyntax f
  let lemId := mkIdent lem
  evalTactic (← `(tactic| refine $lemId $fT (q := $qT) (M := $MT) ?_ ?_ ?_ ?_ ?_ ?_ ?_))
  let gs ← getGoals
  for g in gs do
    setGoals [g]
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``ContinuousOn then
      let t1 ← `(tactic| fun_prop)
      let t2 ← `(tactic| (apply Continuous.continuousOn; fun_prop))
      firstTac [t1, t2]
    else
      evalTactic (← `(tactic| try beta_reduce))
      evalTactic (← `(tactic| first | (norm_num; done) | interval $opts*))
  setGoals []

/-! ### `#realfp_min` / `#realfp_max` -/


/-- `proveArgCore` with the registered functions of the goal. -/
def proveArg (opts : Array (TSyntax `intervalOpt)) : TacticM Unit := withRegistered (proveArgCore opts)

declare_syntax_cat realfpBinder
syntax "(" ident " ∈ " term ")" : realfpBinder

partial def reportGo (maximize : Bool) (bs : Array (TSyntax `realfpBinder)) (body : Term)
    (i : Nat) (vars : Array Expr) (box : Array (ℚ × ℚ)) (names : Array Name) (prec128 : Bool := false) :
      TermElabM Unit := do
  if h : i < bs.size then
    let b := bs[i]
    let x := b.raw[1].getId
    let s ← elabTerm b.raw[3] (some (← mkAppM ``Set #[mkConst ``Real]))
    Term.synthesizeSyntheticMVarsNoPostponing
    let s ← instantiateMVars s
    let (``Set.Icc, #[_, _, l, u]) := (← whnfR s).getAppFnArgs
      | throwError "#realfp_min: {x} must range over `Set.Icc a b`"
    let some ql ← ratOf? l | throwError "#realfp_min: {l} is not a numeral"
    let some qu ← ratOf? u | throwError "#realfp_min: {u} is not a numeral"
    withLocalDeclD x (mkConst ``Real) fun xv =>
      reportGo maximize bs body (i + 1) (vars.push xv) (box.push (ql, qu)) (names.push x) prec128
  else
    let e ← elabTerm body (some (mkConst ``Real))
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let ie ← reify vars e
    let tbl ← runtimeTbl (← entriesIn e)
    if prec128 then
      let g := if maximize then IExpr.neg ie else ie
      let (l, u, arg, nb) := @bnbMinQ tbl g box.toList 20000 (1 / 10 ^ 32)
      let word := if maximize then "maximum" else "minimum"
      let (lo, hi) := if maximize then (-u, -l) else (l, u)
      let pt := String.intercalate ", " ((names.toList.zip arg).map fun (n, v) => s!"{n} ≈ {fmtSig v 36}")
      let gap := hi - lo
      let slack := max gap (1 / 10 ^ 34 * (1 + max |lo| |hi|))
      let below := shortIn (lo - 2 * slack) (lo - slack)
      let above := shortIn (hi + slack) (hi + 2 * slack)
      let (c, w) := if maximize then (above, below) else (below, above)
      let fS ← PrettyPrinter.ppExpr e
      let allB := String.intercalate ", " ((names.toList.zip box.toList).map fun (n, (l, h)) =>
        s!"∀ {n} ∈ Set.Icc ({fmtRat l} : ℝ) {fmtRat h}")
      let exB := String.intercalate ", " ((names.toList.zip box.toList).map fun (n, (l, h)) =>
        s!"∃ {n} ∈ Set.Icc ({fmtRat l} : ℝ) {fmtRat h}")
      let s1 := if maximize then s!"{allB}, {fS} ≤ {fmtRat c}" else s!"{allB}, {fmtRat c} ≤ {fS}"
      let s2 := if maximize then s!"{exB}, {fmtRat w} ≤ {fS}" else s!"{exB}, {fS} ≤ {fmtRat w}"
      logInfo m!"{word} ∈ [{fmtSig lo 36}, {fmtSig hi 36}] (gap {fmtSig gap 3}, {nb} boxes; \
        128-bit enclosures, not a proof)\nattained near {pt}\nstatements `realfp (precision := 128)` \
        should prove:\n  {s1}\n  {s2}"
      return
    let r := @bnbMin tbl ie maximize (boxes box.toList) 50000 1e-9
    let word := if maximize then "maximum" else "minimum"
    let lo := if maximize then -r.upper else r.lower
    let hi := if maximize then -r.lower else r.upper
    let pt := String.intercalate ", " ((names.toList.zip r.arg).map fun (n, v) => s!"{n} ≈ {fmtFloat v}")
    let slack := 1e-6 * (1 + max lo.abs hi.abs)
    let c := (niceRat (if maximize then hi + slack else lo - slack) slack (!maximize)).getD 0
    let w := (niceRat (if maximize then lo - slack else hi + slack) slack maximize).getD 0
    let fS ← PrettyPrinter.ppExpr e
    let allB := String.intercalate ", " ((names.toList.zip box.toList).map fun (n, (l, h)) =>
      s!"∀ {n} ∈ Set.Icc ({fmtRat l} : ℝ) {fmtRat h}")
    let exB := String.intercalate ", " ((names.toList.zip box.toList).map fun (n, (l, h)) =>
      s!"∃ {n} ∈ Set.Icc ({fmtRat l} : ℝ) {fmtRat h}")
    let s1 := if maximize then s!"{allB}, {fS} ≤ {fmtRat c}" else s!"{allB}, {fmtRat c} ≤ {fS}"
    let s2 := if maximize then s!"{exB}, {fmtRat w} ≤ {fS}" else s!"{exB}, {fS} ≤ {fmtRat w}"
    logInfo m!"{word} ∈ [{fmtFloat lo}, {fmtFloat hi}] (gap {fmtFloat (hi - lo)}, {r.boxes} boxes; \
      estimate from the enclosures, not a proof)\nattained near {pt}\nstatements `realfp` \
      should prove:\n  {s1}\n  {s2}"

def realfpReport (maximize : Bool) (bs : Array (TSyntax `realfpBinder)) (body : Term)
    (prec128 : Bool := false) : CommandElabM Unit := liftTermElabM do
  RealFP.requireNative
  reportGo maximize bs body 0 #[] #[] #[] prec128

def precArg (n : TSyntax `num) : CommandElabM Bool := do
  match n.getNat with
  | 64 => pure false
  | 128 => pure true
  | k => throwErrorAt n "#realfp_min: (precision := {k}): expected 64 or 128"

/-- `#realfp_min (x ∈ Set.Icc a b) (y ∈ Set.Icc c d), f x y`: approximate minimum, minimiser
and a bound for `realfp` (branch and bound with the interval enclosures; nothing is proved). -/
elab "#realfp_min " bs:realfpBinder+ ", " e:term : command => realfpReport false bs e
/-- `#realfp_max (x ∈ Set.Icc a b), f x`: like `#realfp_min` for the maximum. -/
elab "#realfp_max " bs:realfpBinder+ ", " e:term : command => realfpReport true bs e
/-- `#realfp_min (precision := 128) (x ∈ Set.Icc a b), f x`: the same search with 128-bit
dyadic enclosures (natural and centred forms), reporting the extremum to about 35 digits. -/
elab "#realfp_min " "(" &"precision" " := " n:num ")" bs:realfpBinder+ ", " e:term : command => do
  realfpReport false bs e (← precArg n)
/-- `#realfp_max (precision := 128) …`: like `#realfp_min (precision := 128)` for the maximum. -/
elab "#realfp_max " "(" &"precision" " := " n:num ")" bs:realfpBinder+ ", " e:term : command => do
  realfpReport true bs e (← precArg n)

end RealFP.Opt
