/-
Touching points: `f ≥ c` (or `f ≤ c`) on a box when the bound is attained at an interior point.

Plain interval bisection cannot prove `f ≥ 0` when `f(p) = 0` at an interior point `p`: every
box containing `p` gets an enclosure whose lower end is slightly negative. A *touch leaf* proves
the bound on a whole box `B ∋ p` instead, by second-order Taylor expansion:

* `f(p)` satisfies the goal (checked on the point enclosure of `p`), and every `∂ₖf(p) = 0`
  (the enclosure of `∂ₖf` at the point `p` is `[0, 0]`, so `p` must be exactly representable
  and the gradient must evaluate exactly in binary64);
* the Hessian is positive semidefinite on all of `B` (negative semidefinite for `f ≤ c`): every
  real symmetric matrix `S` whose entries lie in the interval Hessian enclosures `H` on `B`
  satisfies `uᵀ S u ≥ 0`. The certificate is a rational symmetric `C` (≈ the Hessian at `p`) and
  rational `ρ` with `Σⱼ |Sₖⱼ − Cₖⱼ| ≤ ρₖ` (checked with intervals) and `C − diag ρ` positive
  definite (checked exactly in `ℚ` by the `pos_def` congruence certificate
  `RealFP.PDQ.congrCheckQ`).

Then `f(x) − f(p) = ½ uᵀ S u` with `u = x − p` and `S` built from second partials at points of
`B` (`RealFP.touch_expand`: a coordinate-by-coordinate Taylor/mean-value expansion, so only the
one-variable derivatives `IExpr.deriv` and `hasDerivAt_box` are needed), hence `f(x) ≥ f(p)`.

*Tangent-plane leaves* (`tanOK`, what the tactic emits) drop the zero-gradient condition:
with the same Hessian certificate, `touch_expand_gen` gives
`f(x) ≥ f(p) + ∇f(p)·(x − p)` on `B`, and the goal is checked on the interval enclosure of
that tangent plane over `B`. `f(p)` and `∇f(p)` are evaluated exactly in `ℚ` (`evalQ`) for
expressions built from `+ − × ÷ ⁻¹ |·| ^n`, so rational touching points such as `1/3` work;
otherwise by intervals at the point. Near-touching at an irrational point (a dyadic `p` with a
tiny gradient) works too. A bound attained exactly at an irrational point cannot be proved
this way.

`TCert` is a bisection tree with `MCert` leaves (the usual `interval` certificates), touch
and tangent-plane leaves. Soundness: `RealFP.touchOK_sound`, `RealFP.tanOK_sound`, `RealFP.checkT_sound`, entry
points `RealFP.proveT_le` / `_lt` / `_ge` / `_gt`.
-/
import RealFPMathlib.Opt
import RealFPMathlib.PosDefQ

open Interval64 Interval64.Spec Interval64.KF
open Interval64Proofs.FloatBits

namespace Interval64.KF

set_option linter.concreteInstances false
variable [ExtTbl]

/-- Sum of a list of expressions. -/
def sumE : List IExpr → IExpr
  | [] => .rat 0
  | a :: t => .add a (sumE t)

/-- Second partial derivative: the `min k j`-derivative of `∂_{max k j} e`. -/
def hessE (e : IExpr) (k j : Nat) : IExpr := (e.deriv (max k j)).deriv (min k j)

/-- Hessian enclosures on `env`, row-major `n × n` (entry `k * n + j`). -/
def hessK (e : IExpr) (n : Nat) (env : List KI) : List KI :=
  (List.range (n * n)).map fun t => evalK env (hessE e (t / n) (t % n))

/-- `Σⱼ |s·Hₖⱼ − Cₖⱼ|` as an expression in the Hessian entries (`var (k * n + j)`), `s = −1`
if `neg`. -/
def rowE (n k : Nat) (neg : Bool) (C : List (List ℚ)) : IExpr :=
  sumE ((List.range n).map fun j =>
    .abs (.sub (bif neg then .neg (.var (k * n + j)) else .var (k * n + j))
      (.rat (RealFP.PDQ.qg C k j))))

/-- Data of a touch leaf: the touching point `p`, the rational centre matrix `C`, the radii
`rho`, and the congruence factor `X` for `C − diag rho` (rows of rationals). -/
structure Touch where
  p : List ℚ
  C : List (List ℚ)
  rho : List ℚ
  X : List (List ℚ)
  deriving Repr, Inhabited

/-- Point enclosures of a rational point. -/
def ptK (p : List ℚ) : List KI := p.map KI.ofRat

/-- `P ⊆ X` (both ends of `X` non-NaN). -/
def insideK (P X : KI) : Bool :=
  !isNaN X.lo && !isNaN X.hi && le X.lo P.lo && le P.hi X.hi

/-- The enclosure is `⊆ [0, 0]`. -/
def zeroAt (F : KI) : Bool := gGe zeroHi F && gLe zeroLo F

/-- Check of a touch leaf on the box `env` for the goal predicate `g` (`upper`: `f ≤ c` type,
the Hessian must be negative semidefinite). -/
def touchOK (e : IExpr) (g : KI → Bool) (upper : Bool) (t : Touch) (env : List KI) : Bool :=
  let n := env.length
  let pe := ptK t.p
  Nat.beq t.p.length n &&
  (List.range n).all (fun i => insideK (pe.getD i zeroK) (env.getD i zeroK)) &&
  g (evalK pe e) &&
  domOK env e &&
  (List.range n).all (fun k => domOK env (e.deriv k) && zeroAt (evalK pe (e.deriv k))) &&
  (List.range n).all (fun k =>
    gLe (KI.ofRat (t.rho.getD k 0)).lo (evalK (hessK e n env) (rowE n k upper t.C))) &&
  (List.range n).all (fun i => (List.range n).all fun j =>
    decide (RealFP.PDQ.qg t.C i j = RealFP.PDQ.qg t.C j i)) &&
  RealFP.PDQ.congrCheckQ n (fun i j => RealFP.PDQ.qg t.C i j - if i = j then t.rho.getD i 0 else 0)
    (RealFP.PDQ.qg t.X)

/-- Exact rational value of an expression built from `+ − × ÷ ⁻¹ |·| ^n`, variables and
rational constants at the rational point `p` (`none` for other operations). Division and
inverse use the `x / 0 = 0` convention of both `ℚ` and `ℝ`. -/
def evalQ (p : List ℚ) : IExpr → Option ℚ
  | .var i => some (p.getD i 0)
  | .rat q => some q
  | .add a b => match evalQ p a, evalQ p b with
    | some x, some y => some (x + y) | _, _ => none
  | .sub a b => match evalQ p a, evalQ p b with
    | some x, some y => some (x - y) | _, _ => none
  | .mul a b => match evalQ p a, evalQ p b with
    | some x, some y => some (x * y) | _, _ => none
  | .div a b => match evalQ p a, evalQ p b with
    | some x, some y => some (x / y) | _, _ => none
  | .neg a => match evalQ p a with | some x => some (-x) | none => none
  | .inv a => match evalQ p a with | some x => some x⁻¹ | none => none
  | .abs a => match evalQ p a with | some x => some |x| | none => none
  | .pow a n => match evalQ p a with | some x => some (x ^ n) | none => none
  | _ => none

/-- Enclosure of `e` at the rational point `p`: the exact value (rounded outward) when
`evalQ` succeeds, else interval evaluation on the point enclosures. -/
def ptVal (p : List ℚ) (e : IExpr) : KI :=
  match evalQ p e with
  | some v => KI.ofRat v
  | none => evalK (ptK p) e

/-- The tangent plane `f(p) + Σₖ ∂ₖf(p) (xₖ − pₖ)` in the variables of `tanEnv`:
`var 0 = f(p)`, `var (k+1) = ∂ₖf(p)`, `var (n+k+1) = pₖ`, `var (n+n+k+1) = xₖ`. -/
def tanE (n : Nat) : IExpr :=
  .add (.var 0) (sumE ((List.range n).map fun k =>
    .mul (.var (k + 1)) (.sub (.var (n + n + k + 1)) (.var (n + k + 1)))))

/-- Enclosures of the variables of `tanE`. -/
def tanEnv (e : IExpr) (p : List ℚ) (env : List KI) : List KI :=
  ptVal p e :: ((List.range env.length).map (fun k => ptVal p (e.deriv k)) ++ (ptK p ++ env))

/-- Check of a tangent-plane leaf: the Hessian certificate of `touchOK` on the box, and the
goal predicate on the enclosure of the tangent plane at `p` over the box (no condition on the
gradient: an exactly zero gradient makes the tangent plane the constant `f(p)`). -/
def tanOK (e : IExpr) (g : KI → Bool) (upper : Bool) (t : Touch) (env : List KI) : Bool :=
  let n := env.length
  let pe := ptK t.p
  Nat.beq t.p.length n &&
  (List.range n).all (fun i => insideK (pe.getD i zeroK) (env.getD i zeroK)) &&
  domOK env e &&
  (List.range n).all (fun k => domOK env (e.deriv k)) &&
  g (evalK (tanEnv e t.p env) (tanE n)) &&
  (List.range n).all (fun k =>
    gLe (KI.ofRat (t.rho.getD k 0)).lo (evalK (hessK e n env) (rowE n k upper t.C))) &&
  (List.range n).all (fun i => (List.range n).all fun j =>
    decide (RealFP.PDQ.qg t.C i j = RealFP.PDQ.qg t.C j i)) &&
  RealFP.PDQ.congrCheckQ n (fun i j => RealFP.PDQ.qg t.C i j - if i = j then t.rho.getD i 0 else 0)
    (RealFP.PDQ.qg t.X)

/-- Bisection tree with ordinary (`m`), touch and tangent-plane (`tan`) leaves. -/
inductive TCert where
  | m (c : MCert)
  | split (i : Nat) (m : Nat) (l r : TCert)
  | touch (t : Touch)
  | tan (t : Touch)
  deriving Repr, Inhabited

def checkT (e : IExpr) (g : KI → Bool) (upper : Bool) : TCert → List KI → Bool
  | .m c, env => checkM e g upper c env
  | .split i m l r, env =>
    !isNaN m && Nat.blt m (2 ^ 64) &&
      checkT e g upper l (env.set i ⟨(env.getD i zeroK).lo, m⟩) &&
      checkT e g upper r (env.set i ⟨m, (env.getD i zeroK).hi⟩)
  | .touch t, env => touchOK e g upper t env
  | .tan t, env => tanOK e g upper t env

end Interval64.KF

noncomputable section

namespace RealFP

open Finset Matrix

set_option linter.concreteInstances false
variable [ExtTbl] [ExtSem]

/-! ### One-variable Taylor expansion with Lagrange remainder (in a set `S`) -/

omit [ExtTbl] [ExtSem] in
theorem taylor2 {φ φ' φ'' : ℝ → ℝ} {S : ℝ → Prop} {a b : ℝ}
    (h1 : ∀ t ∈ Set.uIcc a b, HasDerivAt φ (φ' t) t)
    (h2 : ∀ t ∈ Set.uIcc a b, HasDerivAt φ' (φ'' t) t)
    (hS : ∀ t ∈ Set.uIcc a b, S (φ'' t)) :
    ∃ d, S d ∧ 2 * (φ b - φ a - φ' a * (b - a)) = d * (b - a) ^ 2 := by
  have key : ∀ c, c ∈ Set.uIcc a b → c ≠ a →
      (b - a) ^ 2 * (φ' c - φ' a) = (φ b - φ a - φ' a * (b - a)) * (2 * (c - a)) →
      ∃ d, S d ∧ 2 * (φ b - φ a - φ' a * (b - a)) = d * (b - a) ^ 2 := by
    intro c hc hca heq
    have hsub : Set.uIcc a c ⊆ Set.uIcc a b := Set.uIcc_subset_uIcc Set.left_mem_uIcc hc
    obtain ⟨d, hd, hmv⟩ := mvt_uIcc (φ := φ') (S := S) (a := a) (b := c)
      (fun t ht => ⟨_, hS t (hsub ht), h2 t (hsub ht)⟩)
    refine ⟨d, hd, ?_⟩
    have hca' : c - a ≠ 0 := sub_ne_zero.2 hca
    rw [hmv] at heq
    apply mul_right_cancel₀ hca'
    linear_combination -heq
  -- `F(s) = φ s - φ a - φ' a (s - a)`, `G(s) = (s - a)²`
  have hF : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun s => φ s - φ a - φ' a * (s - a))
      (φ' t - φ' a) t := fun t ht =>
    (((h1 t ht).sub_const (φ a)).sub ((hasDerivAt_id' t).sub_const a |>.const_mul (φ' a))).congr_deriv
      (by ring)
  have hG : ∀ t, HasDerivAt (fun s => (s - a) * (s - a)) (2 * (t - a)) t := fun t =>
    (((hasDerivAt_id' t).sub_const a).mul ((hasDerivAt_id' t).sub_const a)).congr_deriv (by ring)
  rcases lt_trichotomy a b with hab | rfl | hab
  · have hI : Set.Icc a b ⊆ Set.uIcc a b := Set.Icc_subset_uIcc
    obtain ⟨c, hc, hce⟩ := exists_ratio_hasDerivAt_eq_ratio_slope
      (fun s => φ s - φ a - φ' a * (s - a)) (fun s => φ' s - φ' a) hab
      (fun t ht => (hF t (hI ht)).continuousAt.continuousWithinAt)
      (fun t ht => hF t (hI (Set.Ioo_subset_Icc_self ht)))
      (fun s => (s - a) * (s - a)) (fun s => 2 * (s - a))
      (fun t _ => (hG t).continuousAt.continuousWithinAt) (fun t _ => hG t)
    refine key c (hI (Set.Ioo_subset_Icc_self hc)) (ne_of_gt hc.1) ?_
    linear_combination hce
  · obtain hS' := hS a Set.left_mem_uIcc
    exact ⟨_, hS', by ring⟩
  · have hI : Set.Icc b a ⊆ Set.uIcc a b := Set.Icc_subset_uIcc'
    obtain ⟨c, hc, hce⟩ := exists_ratio_hasDerivAt_eq_ratio_slope
      (fun s => φ s - φ a - φ' a * (s - a)) (fun s => φ' s - φ' a) hab
      (fun t ht => (hF t (hI ht)).continuousAt.continuousWithinAt)
      (fun t ht => hF t (hI (Set.Ioo_subset_Icc_self ht)))
      (fun s => (s - a) * (s - a)) (fun s => 2 * (s - a))
      (fun t _ => (hG t).continuousAt.continuousWithinAt) (fun t _ => hG t)
    refine key c (hI (Set.Ioo_subset_Icc_self hc)) (ne_of_lt hc.2) ?_
    linear_combination -hce

/-! ### Lists -/

omit [ExtTbl] [ExtSem] in
theorem forall2_of_getD : ∀ {l : List ℝ} {env : List KI}, l.length = env.length →
    (∀ i < env.length, l.getD i 0 ∈ (toI (env.getD i zeroK)).toSet) →
    List.Forall₂ (fun x X => x ∈ (toI X).toSet) l env
  | [], [], _, _ => .nil
  | x :: l, X :: env, hl, h =>
    .cons (by simpa using h 0 (by simp))
      (forall2_of_getD (by simpa using hl) (fun i hi => by simpa using h (i + 1) (by simpa using hi)))
  | [], _ :: _, hl, _ => absurd hl (by simp)
  | _ :: _, [], hl, _ => absurd hl (by simp)

/-- The point that agrees with `xs` in the first `k` coordinates and with `ps` in the rest. -/
def mixL (n k : ℕ) (xs ps : List ℝ) : List ℝ :=
  (List.range n).map fun i => if i < k then xs.getD i 0 else ps.getD i 0

omit [ExtTbl] [ExtSem] in
theorem mixL_length (n k : ℕ) (xs ps : List ℝ) : (mixL n k xs ps).length = n := by simp [mixL]

omit [ExtTbl] [ExtSem] in
theorem mixL_getElem {n k : ℕ} {xs ps : List ℝ} {i : ℕ} (h : i < (mixL n k xs ps).length) :
    (mixL n k xs ps)[i] = if i < k then xs.getD i 0 else ps.getD i 0 := by
  simp [mixL]

omit [ExtTbl] [ExtSem] in
theorem getD_eq_getElem' {l : List ℝ} {i : ℕ} (h : i < l.length) : l.getD i 0 = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

omit [ExtTbl] [ExtSem] in
theorem mixL_getD {n k : ℕ} {xs ps : List ℝ} {i : ℕ} (h : i < n) :
    (mixL n k xs ps).getD i 0 = if i < k then xs.getD i 0 else ps.getD i 0 := by
  have h' : i < (mixL n k xs ps).length := by rw [mixL_length]; exact h
  rw [getD_eq_getElem' h', mixL_getElem]


omit [ExtTbl] [ExtSem] in
theorem mixL_zero {n : ℕ} {xs ps : List ℝ} (hp : ps.length = n) : mixL n 0 xs ps = ps := by
  apply List.ext_getElem (by rw [mixL_length, hp])
  intro i h1 h2
  rw [mixL_getElem]; simp only [Nat.not_lt_zero, ↓reduceIte]; exact getD_eq_getElem' h2

omit [ExtTbl] [ExtSem] in
theorem mixL_full {n : ℕ} {xs ps : List ℝ} (hx : xs.length = n) : mixL n n xs ps = xs := by
  apply List.ext_getElem (by rw [mixL_length, hx])
  intro i h1 h2
  rw [mixL_getElem]
  have : i < n := by rw [mixL_length] at h1; exact h1
  simp only [this, ↓reduceIte]; exact getD_eq_getElem' h2

omit [ExtTbl] [ExtSem] in
theorem mixL_set_succ {n k : ℕ} {xs ps : List ℝ} :
    (mixL n k xs ps).set k (xs.getD k 0) = mixL n (k + 1) xs ps := by
  apply List.ext_getElem (by simp [mixL_length])
  intro i h1 h2
  rw [List.getElem_set, mixL_getElem, mixL_getElem]
  by_cases hik : k = i
  · subst hik; simp
  · simp only [hik, ↓reduceIte]
    by_cases h : i < k
    · simp [h, show i < k + 1 by omega]
    · simp [h, show ¬ i < k + 1 by omega]

omit [ExtTbl] [ExtSem] in
theorem mixL_set_self {n k : ℕ} {xs ps : List ℝ} (hk : k < n) :
    (mixL n k xs ps).set k (ps.getD k 0) = mixL n k xs ps := by
  have h := set_getD_self (xs := mixL n k xs ps) (i := k) (by rw [mixL_length]; exact hk)
  rw [mixL_getD hk] at h; simpa using h

omit [ExtTbl] [ExtSem] in
theorem mixL_mem {env : List KI} {xs ps : List ℝ}
    (hxs : List.Forall₂ (fun x X => x ∈ (toI X).toSet) xs env)
    (hps : List.Forall₂ (fun x X => x ∈ (toI X).toSet) ps env) (k : ℕ) :
    List.Forall₂ (fun x X => x ∈ (toI X).toSet) (mixL env.length k xs ps) env := by
  refine forall2_of_getD (mixL_length _ _ _ _) fun i hi => ?_
  rw [mixL_getD hi]
  split_ifs
  · exact getD_mem_toI hxs i
  · exact getD_mem_toI hps i

/-! ### The quadratic expansion -/

omit [ExtTbl] [ExtSem] in
/-- `Σₖ (2 (Σ_{j<k} bₖⱼ uⱼ) uₖ + aₖ uₖ²) = uᵀ S u` for the symmetric `S` with diagonal `a` and
lower triangle `b`. -/
theorem tri_sum (a : ℕ → ℝ) (b : ℕ → ℕ → ℝ) (u : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ range m, (2 * (∑ j ∈ range k, b k j * u j) * u k + a k * u k ^ 2) =
    ∑ k ∈ range m, ∑ j ∈ range m,
      u k * (if j < k then b k j else if k < j then b j k else a k) * u j := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : ∀ k ∈ range m, ∑ j ∈ range (m + 1),
        u k * (if j < k then b k j else if k < j then b j k else a k) * u j =
        ∑ j ∈ range m, u k * (if j < k then b k j else if k < j then b j k else a k) * u j +
          u k * b m k * u m := by
      intro k hk
      have hk' : k < m := mem_range.1 hk
      rw [sum_range_succ]
      simp [show ¬ m < k by omega, hk']
    have h2 : ∑ j ∈ range (m + 1),
        u m * (if j < m then b m j else if m < j then b j m else a m) * u j =
        ∑ j ∈ range m, u m * b m j * u j + u m * a m * u m := by
      rw [sum_range_succ]
      congr 1
      · exact sum_congr rfl fun j hj => by simp [mem_range.1 hj]
      · simp
    rw [sum_range_succ, ih, sum_range_succ (fun k => ∑ j ∈ range (m + 1), _), sum_congr rfl h1, h2,
      sum_add_distrib]
    have h3 : ∑ k ∈ range m, u k * b m k * u m = (∑ j ∈ range m, b m j * u j) * u m := by
      rw [sum_mul]; exact sum_congr rfl fun j _ => by ring
    have h4 : ∑ j ∈ range m, u m * b m j * u j = (∑ j ∈ range m, b m j * u j) * u m := by
      rw [sum_mul]; exact sum_congr rfl fun j _ => by ring
    rw [h3, h4]; ring

/-- Second-order expansion on a box: if `e` and each `∂ₖe` are differentiable on the box
(`domOK`) and `∇e(p) = 0`, then `2 (e(x) − e(p)) = uᵀ S u` with `u = x − p` and `S` symmetric,
with entries in the Hessian enclosures `hessE` on the box. -/
theorem touch_expand_gen {e : IExpr} {env : List KI} (hw : ∀ X ∈ env, WF X) {xs ps : List ℝ}
    (hxs : List.Forall₂ (fun x X => x ∈ (toI X).toSet) xs env)
    (hps : List.Forall₂ (fun x X => x ∈ (toI X).toSet) ps env)
    (hd0 : domOK env e = true) (hd1 : ∀ k < env.length, domOK env (e.deriv k) = true) :
    ∃ S : ℕ → ℕ → ℝ, (∀ k j, S k j = S j k) ∧
      (∀ k < env.length, ∀ j < env.length, S k j ∈ (toI (evalK env (hessE e k j))).toSet) ∧
      2 * (e.denote xs - e.denote ps) =
        2 * ∑ k ∈ range env.length, (e.deriv k).denote ps * (xs.getD k 0 - ps.getD k 0) +
        ∑ k ∈ range env.length, ∑ j ∈ range env.length,
          (xs.getD k 0 - ps.getD k 0) * S k j * (xs.getD j 0 - ps.getD j 0) := by
  set n := env.length with hn
  set u : ℕ → ℝ := fun i => xs.getD i 0 - ps.getD i 0 with hu
  have hM := mixL_mem hxs hps
  have hlenM : ∀ k, (mixL n k xs ps).length = n := fun k => mixL_length _ _ _ _
  -- mean value steps for the gradient
  have stepA : ∀ k j, ∃ b : ℝ, k < n → j < n →
      b ∈ (toI (evalK env ((e.deriv k).deriv j))).toSet ∧
      (e.deriv k).denote (mixL n (j + 1) xs ps) - (e.deriv k).denote (mixL n j xs ps) =
        b * u j := by
    intro k j
    by_cases hk : k < n
    · by_cases hj : j < n
      · obtain ⟨d, hd, hmv⟩ := mvt_uIcc
          (S := fun d => d ∈ (toI (evalK env ((e.deriv k).deriv j))).toSet)
          (φ := fun s => (e.deriv k).denote ((mixL n j xs ps).set j s))
          (a := ps.getD j 0) (b := xs.getD j 0) (fun t ht => by
            have htX := seg_mem (getD_mem_toI hps j) (getD_mem_toI hxs j) ht
            exact ⟨_, (memK hw (forall2_setx (hM j) j htX) _).1,
              hasDerivAt_box hw (hM j) (by rw [hlenM]; exact hj) (hd1 k hk) htX⟩)
        refine ⟨d, fun _ _ => ⟨hd, ?_⟩⟩
        simp only [mixL_set_succ, mixL_set_self hj] at hmv
        exact hmv
      · exact ⟨0, fun _ h => absurd h hj⟩
    · exact ⟨0, fun h => absurd h hk⟩
  -- Taylor steps along each coordinate
  have stepB : ∀ k, ∃ a : ℝ, k < n →
      a ∈ (toI (evalK env ((e.deriv k).deriv k))).toSet ∧
      2 * (e.denote (mixL n (k + 1) xs ps) - e.denote (mixL n k xs ps) -
        (e.deriv k).denote (mixL n k xs ps) * u k) = a * u k ^ 2 := by
    intro k
    by_cases hk : k < n
    · have hk' : k < (mixL n k xs ps).length := by rw [hlenM]; exact hk
      obtain ⟨d, hd, ht⟩ := taylor2
        (S := fun d => d ∈ (toI (evalK env ((e.deriv k).deriv k))).toSet)
        (φ := fun s => e.denote ((mixL n k xs ps).set k s))
        (φ' := fun s => (e.deriv k).denote ((mixL n k xs ps).set k s))
        (φ'' := fun s => ((e.deriv k).deriv k).denote ((mixL n k xs ps).set k s))
        (a := ps.getD k 0) (b := xs.getD k 0)
        (fun t ht => hasDerivAt_box hw (hM k) hk' hd0
          (seg_mem (getD_mem_toI hps k) (getD_mem_toI hxs k) ht))
        (fun t ht => hasDerivAt_box hw (hM k) hk' (hd1 k hk)
          (seg_mem (getD_mem_toI hps k) (getD_mem_toI hxs k) ht))
        (fun t ht => (memK hw (forall2_setx (hM k) k
          (seg_mem (getD_mem_toI hps k) (getD_mem_toI hxs k) ht)) _).1)
      refine ⟨d, fun _ => ⟨hd, ?_⟩⟩
      simp only [mixL_set_succ, mixL_set_self hk] at ht
      exact ht
    · exact ⟨0, fun h => absurd h hk⟩
  choose b hb using stepA
  choose a ha using stepB
  -- gradient at the intermediate points
  have hgrad : ∀ k < n, (e.deriv k).denote (mixL n k xs ps) =
      (e.deriv k).denote ps + ∑ j ∈ range k, b k j * u j := by
    intro k hk
    have htel := sum_range_sub (fun j => (e.deriv k).denote (mixL n j xs ps)) k
    rw [mixL_zero (by rw [hps.length_eq])] at htel
    have hs : ∑ j ∈ range k, b k j * u j =
        (e.deriv k).denote (mixL n k xs ps) - (e.deriv k).denote ps := by
      rw [← htel]
      exact sum_congr rfl fun j hj => ((hb k j hk (by have := mem_range.1 hj; omega)).2).symm
    linarith
  refine ⟨fun k j => if j < k then b k j else if k < j then b j k else a k, ?_, ?_, ?_⟩
  · intro k j
    rcases lt_trichotomy j k with h | rfl | h
    · simp [h, show ¬ k < j by omega]
    · rfl
    · simp [h, show ¬ j < k by omega]
  · intro k hk j hj
    simp only [hessE]
    rcases lt_trichotomy j k with h | h | h
    · simp only [h, ↓reduceIte, max_eq_left h.le, min_eq_right h.le]; exact (hb k j hk hj).1
    · subst h; simp only [lt_irrefl, ↓reduceIte, max_self, min_self]; exact (ha _ hk).1
    · simp only [show ¬ j < k by omega, h, ↓reduceIte, max_eq_right h.le, min_eq_left h.le]
      exact (hb j k hj hk).1
  · have htel := sum_range_sub (fun k => e.denote (mixL n k xs ps)) n
    rw [mixL_zero (by rw [hps.length_eq]), mixL_full (by rw [hxs.length_eq])] at htel
    rw [← htel, mul_sum, ← tri_sum a b u n, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun k hk => ?_
    have hk' := mem_range.1 hk
    have := (ha k hk').2
    rw [hgrad k hk'] at this
    linear_combination this

/-- Second-order expansion at a stationary point: if `∇e(p) = 0` then
`2 (e(x) − e(p)) = uᵀ S u` (see `touch_expand_gen`). -/
theorem touch_expand {e : IExpr} {env : List KI} (hw : ∀ X ∈ env, WF X) {xs ps : List ℝ}
    (hxs : List.Forall₂ (fun x X => x ∈ (toI X).toSet) xs env)
    (hps : List.Forall₂ (fun x X => x ∈ (toI X).toSet) ps env)
    (hd0 : domOK env e = true) (hd1 : ∀ k < env.length, domOK env (e.deriv k) = true)
    (hgr : ∀ k < env.length, (e.deriv k).denote ps = 0) :
    ∃ S : ℕ → ℕ → ℝ, (∀ k j, S k j = S j k) ∧
      (∀ k < env.length, ∀ j < env.length, S k j ∈ (toI (evalK env (hessE e k j))).toSet) ∧
      2 * (e.denote xs - e.denote ps) =
        ∑ k ∈ range env.length, ∑ j ∈ range env.length,
          (xs.getD k 0 - ps.getD k 0) * S k j * (xs.getD j 0 - ps.getD j 0) := by
  obtain ⟨S, h1, h2, h3⟩ := touch_expand_gen hw hxs hps hd0 hd1
  refine ⟨S, h1, h2, ?_⟩
  rw [h3, sum_eq_zero fun k hk => by rw [hgr k (mem_range.1 hk), zero_mul]]
  ring

/-! ### Positive semidefiniteness of interval matrices -/

omit [ExtTbl] [ExtSem] in
theorem quad_nonneg_of_cert {n : ℕ} (S : ℕ → ℕ → ℝ) (C : ℕ → ℕ → ℚ) (ρ : ℕ → ℚ)
    (X : ℕ → ℕ → ℚ) (hS : ∀ k j, S k j = S j k) (hC : ∀ i j, i < n → j < n → C i j = C j i)
    (hR : ∀ k < n, ∑ j ∈ range n, |S k j - C k j| ≤ ρ k)
    (hPD : PDQ.congrCheckQ n (fun i j => C i j - if i = j then ρ i else 0) X = true)
    (u : ℕ → ℝ) : 0 ≤ ∑ k ∈ range n, ∑ j ∈ range n, u k * S k j * u j := by
  -- `C − diag ρ` is positive definite
  have hA := PDQ.posDef_of_congrQ hPD (fun i j hi hj => by
    by_cases h : i = j
    · subst h; rfl
    · simp only [h, Ne.symm h, ↓reduceIte, hC i j hi hj])
  have hAq : 0 ≤ ∑ k ∈ range n, ∑ j ∈ range n,
      u k * ((C k j : ℝ) - if k = j then (ρ k : ℝ) else 0) * u j := by
    set v : Fin n → ℝ := fun i => u i
    have hq : 0 ≤ star v ⬝ᵥ ((Matrix.of fun i j : Fin n =>
        (((C i j - if (i : ℕ) = j then ρ i else 0 : ℚ)) : ℝ)) *ᵥ v) := by
      by_cases hv : v = 0
      · rw [hv]; simp
      · exact ((Matrix.posDef_iff_dotProduct_mulVec.1 hA).2 hv).le
    rw [Mat.quad_eq] at hq
    have hq' : 0 ≤ ∑ i : Fin n, ∑ l : Fin n,
        u i * ((C i l : ℝ) - if (i : ℕ) = l then (ρ i : ℝ) else 0) * u l := by
      refine le_of_le_of_eq hq (sum_congr rfl fun i _ => sum_congr rfl fun l _ => ?_)
      simp only [v, Matrix.of_apply]; push_cast; split_ifs <;> simp
    have e : ∀ k, ∑ j ∈ range n, u k * ((C k j : ℝ) - if k = j then (ρ k : ℝ) else 0) * u j =
        ∑ j : Fin n, u k * ((C k j : ℝ) - if k = (j : ℕ) then (ρ k : ℝ) else 0) * u j :=
      fun k => Finset.sum_range _
    rw [Finset.sum_range]; simp only [e]; exact hq'
  -- error terms
  set E : ℕ → ℕ → ℝ := fun k j => S k j - (C k j : ℝ) with hE
  have hEs : ∀ k ∈ range n, ∀ j ∈ range n, |E k j| = |E j k| := by
    intro k hk j hj
    simp only [hE, hS k j, hC k j (mem_range.1 hk) (mem_range.1 hj)]
  have hterm : ∀ k j, -(|E k j| * u k ^ 2 + |E k j| * u j ^ 2) / 2 ≤ u k * E k j * u j := by
    intro k j
    have h1 : -(|E k j| * |u k * u j|) ≤ E k j * (u k * u j) := by
      have := neg_abs_le (E k j * (u k * u j)); rwa [abs_mul] at this
    have h2 : 2 * |u k * u j| ≤ u k ^ 2 + u j ^ 2 := by
      rw [abs_mul]; nlinarith [sq_nonneg (|u k| - |u j|), sq_abs (u k), sq_abs (u j)]
    have h3 := abs_nonneg (E k j)
    nlinarith
  have hcomm : ∑ k ∈ range n, ∑ j ∈ range n, |E k j| * u j ^ 2 =
      ∑ k ∈ range n, ∑ j ∈ range n, |E k j| * u k ^ 2 := by
    rw [sum_comm]
    exact sum_congr rfl fun k hk => sum_congr rfl fun j hj => by rw [hEs j hj k hk]
  have hlow : -∑ k ∈ range n, (∑ j ∈ range n, |E k j|) * u k ^ 2 ≤
      ∑ k ∈ range n, ∑ j ∈ range n, u k * E k j * u j := by
    have := sum_le_sum fun k (_ : k ∈ range n) => sum_le_sum fun j (_ : j ∈ range n) => hterm k j
    have e1 : ∑ k ∈ range n, ∑ j ∈ range n, -(|E k j| * u k ^ 2 + |E k j| * u j ^ 2) / 2 =
        -(∑ k ∈ range n, ∑ j ∈ range n, |E k j| * u k ^ 2 +
          ∑ k ∈ range n, ∑ j ∈ range n, |E k j| * u j ^ 2) / 2 := by
      simp only [neg_div, sum_neg_distrib, ← sum_div, sum_add_distrib]
    rw [e1, hcomm] at this
    have e2 : ∑ k ∈ range n, (∑ j ∈ range n, |E k j|) * u k ^ 2 =
        ∑ k ∈ range n, ∑ j ∈ range n, |E k j| * u k ^ 2 := by
      simp only [sum_mul]
    linarith
  have hρ : ∑ k ∈ range n, (∑ j ∈ range n, |E k j|) * u k ^ 2 ≤
      ∑ k ∈ range n, (ρ k : ℝ) * u k ^ 2 :=
    sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (hR k (mem_range.1 hk)) (sq_nonneg _)
  have hsplit : ∑ k ∈ range n, ∑ j ∈ range n, u k * S k j * u j =
      ∑ k ∈ range n, ∑ j ∈ range n, u k * (C k j : ℝ) * u j +
        ∑ k ∈ range n, ∑ j ∈ range n, u k * E k j * u j := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [← sum_add_distrib]
    exact sum_congr rfl fun j _ => by simp only [hE]; ring
  have hdiag : ∑ k ∈ range n, ∑ j ∈ range n,
      u k * ((C k j : ℝ) - if k = j then (ρ k : ℝ) else 0) * u j =
      ∑ k ∈ range n, ∑ j ∈ range n, u k * (C k j : ℝ) * u j -
        ∑ k ∈ range n, (ρ k : ℝ) * u k ^ 2 := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun k hk => ?_
    have : ∑ j ∈ range n, u k * ((C k j : ℝ) - if k = j then (ρ k : ℝ) else 0) * u j =
        ∑ j ∈ range n, u k * (C k j : ℝ) * u j -
          ∑ j ∈ range n, (if k = j then (ρ k : ℝ) * u k ^ 2 else 0) := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun j _ => by split_ifs with h <;> [subst h; skip] <;> ring
    rw [this, sum_ite_eq]; simp [hk]
  linarith


/-! ### Soundness of touch leaves and bisection -/

omit [ExtTbl] [ExtSem] in
theorem insideK_sound {P X : KI} (hp : WF P) (hx : WF X) (h : insideK P X = true)
    {x : ℝ} (hm : x ∈ (toI P).toSet) : x ∈ (toI X).toSet := by
  simp only [insideK, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hln, hhn⟩, hl⟩, hh⟩ := h
  obtain ⟨⟨hpl, hlp⟩, ⟨hph, hhp⟩⟩ := mem_toSet_iff_toE.1 hm
  simp only [toI] at hpl hlp hph hhp
  have hxl : (toF X.lo).isNaN = false := by rw [isNaN_toF hx.1]; exact hln
  have hxh : (toF X.hi).isNaN = false := by rw [isNaN_toF hx.2]; exact hhn
  have h1 : toF X.lo ≤ toF P.lo := by
    have := le_toF hx.1 hp.1; rw [hl] at this; exact of_decide_eq_true this
  have h2 : toF P.hi ≤ toF X.hi := by
    have := le_toF hp.2 hx.2; rw [hh] at this; exact of_decide_eq_true this
  rw [float_le_iff_toE hxl hpl] at h1
  rw [float_le_iff_toE hph hxh] at h2
  exact mem_toSet_of_toE hxl hxh (h1.trans hlp) (hhp.trans h2)

omit [ExtTbl] [ExtSem] in
theorem ptK_wf (p : List ℚ) : ∀ X ∈ ptK p, WF X := by
  intro X h
  obtain ⟨q, _, rfl⟩ := List.mem_map.1 h
  exact (ofRat_toI q).2

/-- The real point of a rational point. -/
def ptR (p : List ℚ) : List ℝ := p.map (fun q : ℚ => (q : ℝ))

omit [ExtTbl] [ExtSem] in
theorem ptK_mem (p : List ℚ) :
    List.Forall₂ (fun x X => x ∈ (toI X).toSet) (ptR p) (ptK p) := by
  unfold ptR
  induction p with
  | nil => exact .nil
  | cons q p ih =>
    refine .cons ?_ ih
    rw [(ofRat_toI q).1]; exact mem_toSet_ofRat q

theorem zeroAt_sound {env : List KI} {xs : List ℝ} (hw : ∀ X ∈ env, WF X)
    (hxs : List.Forall₂ (fun x X => x ∈ (toI X).toSet) xs env) {e : IExpr}
    (h : zeroAt (evalK env e) = true) : e.denote xs = 0 := by
  have m := memK hw hxs e
  simp only [zeroAt, Bool.and_eq_true] at h
  obtain ⟨hl, hh⟩ := h
  have h1 := gGe_sound 0 _ m.2 hl _ m.1
  have h2 := gLe_sound 0 _ m.2 hh _ m.1
  simpa using le_antisymm h2 h1

omit [ExtTbl] [ExtSem] in
theorem lsumR (n : ℕ) (f : ℕ → ℝ) : ((List.range n).map f).sum = ∑ j ∈ range n, f j := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

theorem sumE_denote (xs : List ℝ) (l : List IExpr) :
    (sumE l).denote xs = (l.map (IExpr.denote xs)).sum := by
  induction l with
  | nil => simp [sumE, IExpr.denote]
  | cons a l ih => simp [sumE, IExpr.denote, ih]

/-- An accepted touch leaf proves the goal on the whole box. No floating-point execution,
external solver, or unproved calculus axiom is trusted. -/
theorem touchOK_sound (e : IExpr) (g : KI → Bool) (upper : Bool) (P : ℝ → Prop)
    (hg : ∀ F, WF F → g F = true → ∀ y ∈ (toI F).toSet, P y)
    (hP : ∀ y z, (if upper then z ≤ y else y ≤ z) → P y → P z)
    (t : Touch) (env : List KI) (xs : List ℝ) (hw : ∀ X ∈ env, WF X)
    (hxs : List.Forall₂ (fun x X => x ∈ (toI X).toSet) xs env)
    (h : touchOK e g upper t env = true) : P (e.denote xs) := by
  simp only [touchOK, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hlen, hin⟩, hval⟩, hd0⟩, hd1⟩, hrow⟩, hsym⟩, hpd⟩ := h
  set ps := ptR t.p
  have hlen' : t.p.length = env.length := Nat.eq_of_beq_eq_true hlen
  have hp := ptK_mem t.p
  have hpw := ptK_wf t.p
  have hpbox : List.Forall₂ (fun x X => x ∈ (toI X).toSet) ps env := by
    refine forall2_of_getD (by simp [ps, ptR, hlen']) fun i hi => ?_
    exact insideK_sound (getD_wf hpw i) (getD_wf hw i) (hin i hi) (getD_mem_toI hp i)
  have hgr : ∀ k < env.length, (e.deriv k).denote ps = 0 := fun k hk =>
    zeroAt_sound hpw hp (hd1 k hk).2
  have hv := memK hpw hp e
  have hgoal : P (e.denote ps) := hg _ hv.2 hval _ hv.1
  obtain ⟨S, hS, hSm, hex⟩ := touch_expand hw hxs hpbox hd0 (fun k hk => (hd1 k hk).1) hgr
  set n := env.length
  set vals : List ℝ := (List.range (n * n)).map fun i => S (i / n) (i % n)
  have hH : ∀ X ∈ hessK e n env, WF X := by
    intro X hX
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hX
    exact (evalK_toI hw _).2
  have hvals : List.Forall₂ (fun x X => x ∈ (toI X).toSet) vals (hessK e n env) := by
    apply forall2_of_getD (by simp [vals, hessK])
    intro i hi
    have hi' : i < n * n := by simpa [hessK] using hi
    have hn : 0 < n := by nlinarith
    have hid : i / n < n := (Nat.div_lt_iff_lt_mul hn).2 hi'
    have him : i % n < n := Nat.mod_lt _ hn
    simpa [vals, hessK, List.getD_eq_getElem?_getD, hi'] using hSm (i / n) hid (i % n) him
  have hvalget : ∀ k < n, ∀ j < n, vals.getD (k * n + j) 0 = S k j := by
    intro k hk j hj
    have hi : k * n + j < n * n := by nlinarith
    have hd : (k * n + j) / n = k := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < n), Nat.div_eq_of_lt hj,
        zero_add]
    simp [vals, List.getD_eq_getElem?_getD, hi, hd, Nat.add_mod, Nat.mod_eq_of_lt hj]
  have hrows : ∀ k < n, ∑ j ∈ range n,
      |(if upper then -S k j else S k j) - (PDQ.qg t.C k j : ℝ)| ≤ (t.rho.getD k 0 : ℝ) := by
    intro k hk
    have m := memK hH hvals (rowE n k upper t.C)
    have hr := gLe_sound (t.rho.getD k 0) _ m.2 (hrow k hk) _ m.1
    have er : (rowE n k upper t.C).denote vals = ∑ j ∈ range n,
        |(if upper then -S k j else S k j) - (PDQ.qg t.C k j : ℝ)| := by
      rw [rowE, sumE_denote, List.map_map, lsumR]
      refine sum_congr rfl fun j hj => ?_
      have hv := hvalget k hk j (mem_range.1 hj)
      rw [List.getD_eq_getElem?_getD] at hv
      cases upper <;> simp [IExpr.denote, hv]
    rwa [er] at hr
  have hnon := quad_nonneg_of_cert (n := n) (fun k j => if upper then -S k j else S k j)
    (PDQ.qg t.C) (fun k => t.rho.getD k 0) (PDQ.qg t.X)
    (fun k j => by rw [hS k j]) (fun i j hi hj => hsym i hi j hj) hrows hpd (fun k => xs.getD k 0 - ps.getD k 0)
  apply hP _ _ ?_ hgoal
  cases upper
  · simp only [Bool.false_eq_true, ↓reduceIte] at hnon ⊢
    linarith
  · simp only [↓reduceIte] at hnon ⊢
    have he : (∑ k ∈ range n, ∑ j ∈ range n,
        (xs.getD k 0 - ps.getD k 0) * -S k j * (xs.getD j 0 - ps.getD j 0)) =
        -(∑ k ∈ range n, ∑ j ∈ range n,
          (xs.getD k 0 - ps.getD k 0) * S k j * (xs.getD j 0 - ps.getD j 0)) := by
      simp only [mul_neg, neg_mul, sum_neg_distrib]
    rw [he] at hnon
    linarith

/-! ### Exact rational evaluation and tangent-plane leaves -/

omit [ExtTbl] [ExtSem] in
theorem ptR_getD (p : List ℚ) (i : ℕ) : (ptR p).getD i 0 = ((p.getD i 0 : ℚ) : ℝ) := by
  simp only [ptR, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases p[i]? <;> simp

theorem evalQ_sound (p : List ℚ) (e : IExpr) :
    ∀ v : ℚ, evalQ p e = some v → e.denote (ptR p) = (v : ℝ) := by
  induction e with
  | var i => intro v h; simp only [evalQ, Option.some.injEq] at h; subst h; exact ptR_getD p i
  | rat q => intro v h; simp only [evalQ, Option.some.injEq] at h; subst h; rfl
  | add a b iha ihb =>
    intro v h; simp only [evalQ] at h
    cases ha : evalQ p a <;> cases hb : evalQ p b <;> simp only [ha, hb, reduceCtorEq,
      Option.some.injEq] at h
    subst h; simp [IExpr.denote, iha _ ha, ihb _ hb]
  | sub a b iha ihb =>
    intro v h; simp only [evalQ] at h
    cases ha : evalQ p a <;> cases hb : evalQ p b <;> simp only [ha, hb, reduceCtorEq,
      Option.some.injEq] at h
    subst h; simp [IExpr.denote, iha _ ha, ihb _ hb]
  | mul a b iha ihb =>
    intro v h; simp only [evalQ] at h
    cases ha : evalQ p a <;> cases hb : evalQ p b <;> simp only [ha, hb, reduceCtorEq,
      Option.some.injEq] at h
    subst h; simp [IExpr.denote, iha _ ha, ihb _ hb]
  | div a b iha ihb =>
    intro v h; simp only [evalQ] at h
    cases ha : evalQ p a <;> cases hb : evalQ p b <;> simp only [ha, hb, reduceCtorEq,
      Option.some.injEq] at h
    subst h; simp [IExpr.denote, iha _ ha, ihb _ hb]
  | neg a iha =>
    intro v h; simp only [evalQ] at h
    cases ha : evalQ p a <;> simp only [ha, reduceCtorEq, Option.some.injEq] at h
    subst h; simp [IExpr.denote, iha _ ha]
  | inv a iha =>
    intro v h; simp only [evalQ] at h
    cases ha : evalQ p a <;> simp only [ha, reduceCtorEq, Option.some.injEq] at h
    subst h; simp [IExpr.denote, iha _ ha]
  | abs a iha =>
    intro v h; simp only [evalQ] at h
    cases ha : evalQ p a <;> simp only [ha, reduceCtorEq, Option.some.injEq] at h
    subst h; simp [IExpr.denote, iha _ ha]
  | pow a n iha =>
    intro v h; simp only [evalQ] at h
    cases ha : evalQ p a <;> simp only [ha, reduceCtorEq, Option.some.injEq] at h
    subst h; simp [IExpr.denote, iha _ ha]
  | _ => intro v h; simp [evalQ] at h

theorem ptVal_mem (p : List ℚ) (e : IExpr) :
    e.denote (ptR p) ∈ (toI (ptVal p e)).toSet ∧ WF (ptVal p e) := by
  unfold ptVal
  split
  · next v h =>
    rw [evalQ_sound p e v h, (ofRat_toI v).1]
    exact ⟨mem_toSet_ofRat v, (ofRat_toI v).2⟩
  · exact memK (ptK_wf p) (ptK_mem p) e

/-- Real values matching `tanEnv`. -/
def tanVals (e : IExpr) (n : ℕ) (ps xs : List ℝ) : List ℝ :=
  e.denote ps :: ((List.range n).map (fun k => (e.deriv k).denote ps) ++ (ps ++ xs))

theorem tanVals_mem (e : IExpr) (p : List ℚ) (env : List KI) (xs : List ℝ)
    (hxs : List.Forall₂ (fun x X => x ∈ (toI X).toSet) xs env) :
    List.Forall₂ (fun x X => x ∈ (toI X).toSet) (tanVals e env.length (ptR p) xs)
      (tanEnv e p env) := by
  refine .cons (ptVal_mem p e).1 (List.rel_append ?_ (List.rel_append (ptK_mem p) hxs))
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  exact fun k _ => (ptVal_mem p (e.deriv k)).1

theorem tanEnv_wf (e : IExpr) (p : List ℚ) (env : List KI) (hw : ∀ X ∈ env, WF X) :
    ∀ X ∈ tanEnv e p env, WF X := by
  intro X hX
  simp only [tanEnv, List.mem_cons, List.mem_append, List.mem_map, List.mem_range] at hX
  rcases hX with rfl | ⟨k, _, rfl⟩ | hX | hX
  · exact (ptVal_mem p e).2
  · exact (ptVal_mem p (e.deriv k)).2
  · exact ptK_wf p X hX
  · exact hw X hX

theorem tanE_denote (e : IExpr) {n : ℕ} {ps xs : List ℝ} (hp : ps.length = n) :
    (tanE n).denote (tanVals e n ps xs) =
      e.denote ps + ∑ k ∈ range n, (e.deriv k).denote ps * (xs.getD k 0 - ps.getD k 0) := by
  rw [tanE, IExpr.denote, sumE_denote, List.map_map, lsumR]
  congr 1
  refine sum_congr rfl fun k hk => ?_
  have hk' := mem_range.1 hk
  simp only [Function.comp, IExpr.denote, tanVals]
  rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ]
  have hl : ((List.range n).map (fun k => (e.deriv k).denote ps)).length = n := by simp
  set D := (List.range n).map (fun k => (e.deriv k).denote ps)
  have e1 : (D ++ (ps ++ xs))[k]? = some ((e.deriv k).denote ps) := by
    rw [List.getElem?_append_left (by omega)]; simp [D, hk']
  have e2 : (D ++ (ps ++ xs))[n + k]? = ps[k]? := by
    rw [List.getElem?_append_right (by omega), hl, List.getElem?_append_left (by omega)]
    congr 1; omega
  have e3 : (D ++ (ps ++ xs))[n + n + k]? = xs[k]? := by
    rw [List.getElem?_append_right (by omega), hl, List.getElem?_append_right (by omega), hp]
    congr 1; omega
  simp only [List.getD_eq_getElem?_getD, e1, e2, e3, Option.getD_some]

/-- An accepted tangent-plane leaf proves the goal on the whole box: by `touch_expand_gen`
and the Hessian certificate, `f(x) ≥ f(p) + ∇f(p)·(x − p)` (`≤` for upper bounds), and the
goal holds on the enclosure of the right-hand side. -/
theorem tanOK_sound (e : IExpr) (g : KI → Bool) (upper : Bool) (P : ℝ → Prop)
    (hg : ∀ F, WF F → g F = true → ∀ y ∈ (toI F).toSet, P y)
    (hP : ∀ y z, (if upper then z ≤ y else y ≤ z) → P y → P z)
    (t : Touch) (env : List KI) (xs : List ℝ) (hw : ∀ X ∈ env, WF X)
    (hxs : List.Forall₂ (fun x X => x ∈ (toI X).toSet) xs env)
    (h : tanOK e g upper t env = true) : P (e.denote xs) := by
  simp only [tanOK, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hlen, hin⟩, hd0⟩, hd1⟩, hval⟩, hrow⟩, hsym⟩, hpd⟩ := h
  set ps := ptR t.p
  have hlen' : t.p.length = env.length := Nat.eq_of_beq_eq_true hlen
  have hp := ptK_mem t.p
  have hpw := ptK_wf t.p
  have hpbox : List.Forall₂ (fun x X => x ∈ (toI X).toSet) ps env := by
    refine forall2_of_getD (by simp [ps, ptR, hlen']) fun i hi => ?_
    exact insideK_sound (getD_wf hpw i) (getD_wf hw i) (hin i hi) (getD_mem_toI hp i)
  have hpl : ps.length = env.length := by simp [ps, ptR, hlen']
  set n := env.length
  have hT := memK (tanEnv_wf e t.p env hw) (tanVals_mem e t.p env xs hxs) (tanE n)
  rw [tanE_denote e hpl] at hT
  have hgoal := hg _ hT.2 hval _ hT.1
  obtain ⟨S, hS, hSm, hex⟩ := touch_expand_gen hw hxs hpbox hd0 hd1
  set vals : List ℝ := (List.range (n * n)).map fun i => S (i / n) (i % n)
  have hH : ∀ X ∈ hessK e n env, WF X := by
    intro X hX
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hX
    exact (evalK_toI hw _).2
  have hvals : List.Forall₂ (fun x X => x ∈ (toI X).toSet) vals (hessK e n env) := by
    apply forall2_of_getD (by simp [vals, hessK])
    intro i hi
    have hi' : i < n * n := by simpa [hessK] using hi
    have hn : 0 < n := by nlinarith
    have hid : i / n < n := (Nat.div_lt_iff_lt_mul hn).2 hi'
    have him : i % n < n := Nat.mod_lt _ hn
    simpa [vals, hessK, List.getD_eq_getElem?_getD, hi'] using hSm (i / n) hid (i % n) him
  have hvalget : ∀ k < n, ∀ j < n, vals.getD (k * n + j) 0 = S k j := by
    intro k hk j hj
    have hi : k * n + j < n * n := by nlinarith
    have hd : (k * n + j) / n = k := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < n), Nat.div_eq_of_lt hj,
        zero_add]
    simp [vals, List.getD_eq_getElem?_getD, hi, hd, Nat.add_mod, Nat.mod_eq_of_lt hj]
  have hrows : ∀ k < n, ∑ j ∈ range n,
      |(if upper then -S k j else S k j) - (PDQ.qg t.C k j : ℝ)| ≤ (t.rho.getD k 0 : ℝ) := by
    intro k hk
    have m := memK hH hvals (rowE n k upper t.C)
    have hr := gLe_sound (t.rho.getD k 0) _ m.2 (hrow k hk) _ m.1
    have er : (rowE n k upper t.C).denote vals = ∑ j ∈ range n,
        |(if upper then -S k j else S k j) - (PDQ.qg t.C k j : ℝ)| := by
      rw [rowE, sumE_denote, List.map_map, lsumR]
      refine sum_congr rfl fun j hj => ?_
      have hv := hvalget k hk j (mem_range.1 hj)
      rw [List.getD_eq_getElem?_getD] at hv
      cases upper <;> simp [IExpr.denote, hv]
    rwa [er] at hr
  have hnon := quad_nonneg_of_cert (n := n) (fun k j => if upper then -S k j else S k j)
    (PDQ.qg t.C) (fun k => t.rho.getD k 0) (PDQ.qg t.X)
    (fun k j => by rw [hS k j]) (fun i j hi hj => hsym i hi j hj) hrows hpd
    (fun k => xs.getD k 0 - ps.getD k 0)
  apply hP _ _ ?_ hgoal
  cases upper
  · simp only [Bool.false_eq_true, ↓reduceIte] at hnon ⊢
    linarith
  · simp only [↓reduceIte] at hnon ⊢
    have he : (∑ k ∈ range n, ∑ j ∈ range n,
        (xs.getD k 0 - ps.getD k 0) * -S k j * (xs.getD j 0 - ps.getD j 0)) =
        -(∑ k ∈ range n, ∑ j ∈ range n,
          (xs.getD k 0 - ps.getD k 0) * S k j * (xs.getD j 0 - ps.getD j 0)) := by
      simp only [mul_neg, neg_mul, sum_neg_distrib]
    rw [he] at hnon
    linarith

theorem checkT_sound : ∀ (c : TCert) (e : IExpr) (g : KI → Bool) (upper : Bool) (P : ℝ → Prop),
    (∀ F, WF F → g F = true → ∀ y ∈ (toI F).toSet, P y) →
    (∀ y z, (if upper then z ≤ y else y ≤ z) → P y → P z) →
    ∀ (env : List KI) (xs : List ℝ), (∀ X ∈ env, WF X) →
      List.Forall₂ (fun x X => x ∈ (toI X).toSet) xs env →
      checkT e g upper c env = true → P (e.denote xs) := by
  intro c
  induction c with
  | m c =>
    intro e g upper P hg hP env xs hw hxs hc
    exact checkM_sound c e g upper P hg hP env xs hw hxs hc
  | touch t =>
    intro e g upper P hg hP env xs hw hxs hc
    exact touchOK_sound e g upper P hg hP t env xs hw hxs hc
  | tan t =>
    intro e g upper P hg hP env xs hw hxs hc
    exact tanOK_sound e g upper P hg hP t env xs hw hxs hc
  | split i m l r ihl ihr =>
    intro e g upper P hg hP env xs hw hxs hc
    simp only [checkT, Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨⟨⟨hn, hm⟩, hcl⟩, hcr⟩ := hc
    have hm' : m < 2 ^ 64 := Nat.blt_eq ▸ hm
    have hwi := getD_wf hw i
    have hx := getD_mem_toI hxs i
    generalize env.getD i zeroK = X at hx hwi hcl hcr
    rcases split_mem (lo := X.lo) (hi := X.hi) hm' hn hx with h1 | h1
    · exact ihl e g upper P hg hP (env.set i ⟨X.lo, m⟩) xs
        (set_wf hw i (Y := ⟨X.lo, m⟩) ⟨hwi.1, hm'⟩) (forall2_set hxs i (Y := ⟨X.lo, m⟩) h1) hcl
    · exact ihr e g upper P hg hP (env.set i ⟨m, X.hi⟩) xs
        (set_wf hw i (Y := ⟨m, X.hi⟩) ⟨hm', hwi.2⟩) (forall2_set hxs i (Y := ⟨m, X.hi⟩) h1) hcr

theorem proveT_le (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : TCert)
    (h : checkT e (gLe (KI.ofRat c).lo) true cert (boxes bs) = true) (xs : List ℝ)
    (hxs : InBoxes xs bs) : e.denote xs ≤ (c : ℝ) :=
  checkT_sound cert e _ true (fun y => y ≤ (c : ℝ)) (gLe_sound c)
    (fun y z h hy => by simp only [↓reduceIte] at h; linarith) _ xs (boxes_wf bs) (boxes_mem hxs) h

theorem proveT_ge (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : TCert)
    (h : checkT e (gGe (KI.ofRat c).hi) false cert (boxes bs) = true) (xs : List ℝ)
    (hxs : InBoxes xs bs) : (c : ℝ) ≤ e.denote xs :=
  checkT_sound cert e _ false (fun y => (c : ℝ) ≤ y) (gGe_sound c)
    (fun y z h hy => by simp only [Bool.false_eq_true, ↓reduceIte] at h; linarith) _ xs
    (boxes_wf bs) (boxes_mem hxs) h

theorem proveT_lt (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : TCert)
    (h : checkT e (gLt (KI.ofRat c).lo) true cert (boxes bs) = true) (xs : List ℝ)
    (hxs : InBoxes xs bs) : e.denote xs < (c : ℝ) :=
  checkT_sound cert e _ true (fun y => y < (c : ℝ)) (gLt_sound c)
    (fun y z h hy => by simp only [↓reduceIte] at h; linarith) _ xs (boxes_wf bs) (boxes_mem hxs) h

theorem proveT_gt (e : IExpr) (bs : List (ℚ × ℚ)) (c : ℚ) (cert : TCert)
    (h : checkT e (gGt (KI.ofRat c).hi) false cert (boxes bs) = true) (xs : List ℝ)
    (hxs : InBoxes xs bs) : (c : ℝ) < e.denote xs :=
  checkT_sound cert e _ false (fun y => (c : ℝ) < y) (gGt_sound c)
    (fun y z h hy => by simp only [Bool.false_eq_true, ↓reduceIte] at h; linarith) _ xs
    (boxes_wf bs) (boxes_mem hxs) h

omit [ExtSem] in
theorem checkT_m_of (e : IExpr) (g : KI → Bool) (upper : Bool) (c : MCert) (env : List KI)
    (h : checkM e g upper c env = true) : checkT e g upper (.m c) env = true := h

omit [ExtSem] in
theorem checkT_split_of {e : IExpr} {g : KI → Bool} {upper : Bool} {i m : Nat} {l r : TCert}
    {env : List KI} (hm : (!isNaN m && Nat.blt m (2 ^ 64)) = true)
    (hl : checkT e g upper l (env.set i ⟨(env.getD i zeroK).lo, m⟩) = true)
    (hr : checkT e g upper r (env.set i ⟨m, (env.getD i zeroK).hi⟩) = true) :
    checkT e g upper (.split i m l r) env = true := by
  simp only [checkT, hl, hr, Bool.and_true]; exact hm

end RealFP
