/-
Fixed-point Taylor models with a step-by-step product certificate: fast kernel checking of
`integral_bound (precision := 128)`.

A model `⟨c, r⟩` on a cell (centre `m`, `|t - m| ≤ hn / 2^K`) stands for the polynomial
`Σ (cₖ / 2^K) (t - m)^k` with integer `cₖ` and the remainder bound `|f t - p (t - m)| ≤ r / 2^K`
(`FMok`). Arithmetic is on `Int`/`Nat` only (GMP-accelerated in the kernel); products round each
kept coefficient down and add every dropped part to the remainder.

**Certificate.** All products go through an oracle `mo`. The checker `moChk` takes the next
product from a supplied list `ws` and accepts it only if it equals `FM.mul C A B`; the generator
`moGen` (used by the tactic, natively) records the products. In the kernel every product is then
checked once on literal inputs, and later steps use the literal result instead of re-evaluating
it. Soundness is proved for any oracle that returns true products (`MoOK`).

Main result: `integral_bounds_of_quadBoundF`.
-/
import RealFPMathlib.I128TM

open Interval64 Interval64.KF
open Interval128.Dy (Dy DI)
open Finset

namespace Interval128.F

/-! ### Computable part -/

/-- `⌈a / b⌉` on `Nat`. -/
def cdiv (a b : Nat) : Nat := (a + b - 1) / b

/-- `⌊q⌋` and `⌈q⌉` for rationals (kernel-friendly). -/
def floorQ (q : Rat) : Int := q.num / (q.den : Int)
def ceilQ (q : Rat) : Int := -floorQ (-q)

/-- Fixed-point Taylor model: coefficients `c` (scaled by `2^K`) and remainder `r` (scaled). -/
structure FM where
  c : List Int
  r : Nat
deriving DecidableEq, Repr

/-- Cell: order `N`, precision `K`, centre `m`, half-width bound `hn / 2^K`. -/
structure Cell where
  N : Nat
  K : Nat
  m : Rat
  hn : Nat

/-- Upper bound for `ρ^k · 2^K`, `ρ = hn / 2^K`. -/
def pw (C : Cell) (k : Nat) : Nat := cdiv (C.hn ^ k * 2 ^ C.K) (2 ^ (C.K * k))

/-- `Σ |lᵢ| · pw (k + i)`. -/
def adot (C : Cell) : List Int → Nat → Nat
  | [], _ => 0
  | a :: l, k => a.natAbs * pw C k + adot C l (k + 1)

def addL : List Int → List Int → List Int
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: addL p q

def mulL : List Int → List Int → List Int
  | [], _ => []
  | a :: p, q => addL (q.map (a * ·)) (0 :: mulL p q)

def FM.add (A B : FM) : FM := ⟨addL A.c B.c, A.r + B.r⟩
def FM.neg (A : FM) : FM := ⟨A.c.map (- ·), A.r⟩
def FM.sub (A B : FM) : FM := FM.add A B.neg
def FM.addR (A : FM) (n : Nat) : FM := ⟨A.c, A.r + n⟩
def FM.tail (A : FM) : FM := ⟨0 :: A.c.tail, A.r⟩

/-- Product keeping `N` coefficients (rounded down); everything dropped goes to the remainder. -/
def FM.mul (C : Cell) (A B : FM) : FM :=
  let d := mulL A.c B.c
  let lo := d.take C.N
  let S : Int := 2 ^ C.K
  ⟨lo.map (· / S), cdiv (adot C (lo.map (· % S)) 0 + adot C (d.drop C.N) C.N +
      adot C A.c 0 * B.r + adot C B.c 0 * A.r) (2 ^ C.K * 2 ^ C.K) + cdiv (A.r * B.r) (2 ^ C.K)⟩

def constQ (C : Cell) (q : Rat) : FM := ⟨[floorQ (q * 2 ^ C.K)], 1⟩

def constDI (C : Cell) (X : DI) : Option FM :=
  match X.lo, X.hi with
  | some a, some b =>
    let qa := Interval128.Dy.toRat a
    let qb := Interval128.Dy.toRat b
    some ⟨[floorQ ((qa + qb) / 2 * 2 ^ C.K)], (ceilQ ((qb - qa) / 2 * 2 ^ C.K)).toNat + 1⟩
  | _, _ => none

def var (C : Cell) : FM := ⟨[floorQ (C.m * 2 ^ C.K), 2 ^ C.K], 1⟩

/-- Remainder `q ≥ 0` in units of `2^-K` (rounded up). -/
def remN (C : Cell) (q : Rat) : Nat := (ceilQ (q * 2 ^ C.K)).toNat

/-- Bound on `|f|` over the cell. -/
def magF (C : Cell) (A : FM) : Rat := ((cdiv (adot C A.c 0) (2 ^ C.K) + A.r : Nat) : Rat) / 2 ^ C.K

/-- Centre value `c₀ / 2^K`. -/
def head (C : Cell) (A : FM) : Rat := (A.c.headD 0 : Rat) / 2 ^ C.K

/-- Product oracle: consumes / produces certificate entries. -/
abbrev MO := Cell → FM → FM → List FM → Option (FM × List FM)

/-- Checker: the next entry must be the product. -/
def moChk : MO := fun C A B ws =>
  match ws with
  | W :: ws' => if W = FM.mul C A B then some (W, ws') else none
  | [] => none

/-- Generator: computes the product and records it (reversed). -/
def moGen : MO := fun C A B ws => let W := FM.mul C A B; some (W, W :: ws)

/-- Direct evaluation (no certificate). -/
def moDir : MO := fun C A B ws => some (FM.mul C A B, ws)

section
variable (mo : MO) (C : Cell)

def powF (A : FM) : Nat → List FM → Option (FM × List FM)
  | 0, ws => some (constQ C 1, ws)
  | n + 1, ws => match powF A n ws with
    | some (P, ws1) => mo C P A ws1
    | none => none

/-- `Σ cₖ gᵏ` (Horner). -/
def serF (G : FM) : List Rat → List FM → Option (FM × List FM)
  | [], ws => some (⟨[], 0⟩, ws)
  | c :: cs, ws => match serF G cs ws with
    | some (S, ws1) => match mo C G S ws1 with
      | some (P, ws2) => some (FM.add (constQ C c) P, ws2)
      | none => none
    | none => none

def expF (A : FM) (ws : List FM) : Option (FM × List FM) :=
  let G := A.tail
  let r := magF C G
  if r ≤ 1 then
    match constDI C (DI.exp (DI.ofRat (head C A))) with
    | some E =>
      match serF mo C G (Interval128.Dy.coefs Interval128.Dy.expCoef 0 (C.N + 1)) ws with
      | some (S, ws1) => mo C E (S.addR (remN C (Interval128.Dy.expRem r (C.N + 1)))) ws1
      | none => none
    | none => none
  else none

/-- `sin` (`cosQ = false`) or `cos`. -/
def sinCosF (cosQ : Bool) (A : FM) (ws : List FM) : Option (FM × List FM) :=
  let G := A.tail
  let r := magF C G
  if r ≤ 1 then
    match constDI C (DI.sinCos false (DI.ofRat (head C A))),
        constDI C (DI.sinCos true (DI.ofRat (head C A))) with
    | some S0, some C0 =>
      let b := remN C (Interval128.Dy.expRem r (C.N + 1))
      match serF mo C G (Interval128.Dy.coefs Interval128.Dy.cosCoef 0 (C.N + 1)) ws with
      | some (cg, ws1) =>
        match serF mo C G (Interval128.Dy.coefs Interval128.Dy.sinCoef 0 (C.N + 1)) ws1 with
        | some (sg, ws2) =>
          if cosQ then
            match mo C C0 (cg.addR b) ws2 with
            | some (P, ws3) => match mo C S0 (sg.addR b) ws3 with
              | some (Q, ws4) => some (FM.sub P Q, ws4)
              | none => none
            | none => none
          else
            match mo C S0 (cg.addR b) ws2 with
            | some (P, ws3) => match mo C C0 (sg.addR b) ws3 with
              | some (Q, ws4) => some (FM.add P Q, ws4)
              | none => none
            | none => none
        | none => none
      | none => none
    | _, _ => none
  else none

/-- `u = (f - p₀) / p₀` with `|u| ≤ r < 1`, and an enclosure `I0 ∋ 1 / p₀`. -/
def relF (A : FM) (ws : List FM) : Option ((FM × FM × Rat) × List FM) :=
  if head C A ≠ 0 then
    match constDI C (DI.inv (DI.ofRat (head C A))) with
    | some I0 => match mo C I0 A.tail ws with
      | some (U, ws1) => if magF C U < 1 then some ((I0, U, magF C U), ws1) else none
      | none => none
    | none => none
  else none

def invF (A : FM) (ws : List FM) : Option (FM × List FM) :=
  match relF mo C A ws with
  | some ((I0, U, r), ws1) =>
    match serF mo C U (Interval128.Dy.coefs Interval128.Dy.geoCoef 0 (C.N + 1)) ws1 with
    | some (S, ws2) => mo C I0 (S.addR (remN C (r ^ (C.N + 1) / (1 - r)))) ws2
    | none => none
  | none => none

def logF (A : FM) (ws : List FM) : Option (FM × List FM) :=
  if 0 < head C A then
    match relF mo C A ws, DI.log? (DI.ofRat (head C A)) with
    | some ((_, U, r), ws1), some Y =>
      match constDI C Y with
      | some L =>
        match serF mo C U (Interval128.Dy.coefs Interval128.Dy.lnCoef 0 (C.N + 2)) ws1 with
        | some (S, ws2) => some (FM.add L (S.addR (remN C (r ^ (C.N + 2) / (1 - r)))), ws2)
        | none => none
      | none => none
    | _, _ => none
  else none

/-- Model of `e` (variable `0`) on the cell. -/
def tmF : IExpr → List FM → Option (FM × List FM)
  | .var i, ws => if i = 0 then some (var C, ws) else none
  | .rat q, ws => some (constQ C q, ws)
  | .pi, ws => (constDI C DI.pi).map (·, ws)
  | .add a b, ws => match tmF a ws with
    | some (A, ws1) => match tmF b ws1 with
      | some (B, ws2) => some (FM.add A B, ws2)
      | none => none
    | none => none
  | .sub a b, ws => match tmF a ws with
    | some (A, ws1) => match tmF b ws1 with
      | some (B, ws2) => some (FM.sub A B, ws2)
      | none => none
    | none => none
  | .mul a b, ws => match tmF a ws with
    | some (A, ws1) => match tmF b ws1 with
      | some (B, ws2) => mo C A B ws2
      | none => none
    | none => none
  | .div a b, ws => match tmF a ws with
    | some (A, ws1) => match tmF b ws1 with
      | some (B, ws2) => match invF mo C B ws2 with
        | some (IB, ws3) => mo C A IB ws3
        | none => none
      | none => none
    | none => none
  | .neg a, ws => match tmF a ws with
    | some (A, ws1) => some (FM.neg A, ws1)
    | none => none
  | .inv a, ws => match tmF a ws with
    | some (A, ws1) => invF mo C A ws1
    | none => none
  | .pow a n, ws => match tmF a ws with
    | some (A, ws1) => powF mo C A n ws1
    | none => none
  | .exp a, ws => match tmF a ws with
    | some (A, ws1) => expF mo C A ws1
    | none => none
  | .log a, ws => match tmF a ws with
    | some (A, ws1) => logF mo C A ws1
    | none => none
  | .sin a, ws => match tmF a ws with
    | some (A, ws1) => sinCosF mo C false A ws1
    | none => none
  | .cos a, ws => match tmF a ws with
    | some (A, ws1) => sinCosF mo C true A ws1
    | none => none
  | _, _ => none

end

/-- `Σ cₖ (b^(k+i+1) - a^(k+i+1)) / (k+i+1)`. -/
def intQ (a b : Rat) : Nat → List Int → Rat
  | _, [] => 0
  | k, c :: l => c * ((b ^ (k + 1) - a ^ (k + 1)) / (k + 1)) + intQ a b (k + 1) l

/-- The cell `[lo, hi]` at order `N`, precision `K`. -/
def mkCell (N K : Nat) (lo hi : Rat) : Cell :=
  ⟨N, K, (lo + hi) / 2, (ceilQ ((hi - lo) / 2 * 2 ^ K)).toNat⟩

/-- Enclosure `[l, h]` of `∫_lo^hi e`. -/
def cellF (mo : MO) (N K : Nat) (e : IExpr) (lo hi : Rat) (ws : List FM) :
    Option ((Rat × Rat) × List FM) :=
  let C := mkCell N K lo hi
  match tmF mo C e ws with
  | some (A, ws1) =>
    let P := intQ (lo - C.m) (hi - C.m) 0 A.c / 2 ^ K
    let E := (A.r : Rat) / 2 ^ K * (hi - lo)
    some ((P - E, P + E), ws1)
  | none => none

def quadF (mo : MO) (N K : Nat) (e : IExpr) : Rat → List Rat → List FM →
    Option ((Rat × Rat) × List FM)
  | _, [], ws => some ((0, 0), ws)
  | lo, hi :: rest, ws => match cellF mo N K e lo hi ws with
    | some ((l1, h1), ws1) => match quadF mo N K e hi rest ws1 with
      | some ((l2, h2), ws2) => some ((l1 + l2, h1 + h2), ws2)
      | none => none
    | none => none

/-- Certificate witnesses (all products, in checking order), computed natively. -/
def witnesses (N K : Nat) (e : IExpr) (qa : Rat) (ds : List Rat) : List FM :=
  match quadF moGen N K e qa ds [] with
  | some (_, ws) => ws.reverse
  | none => []

set_option linter.concreteInstances false
variable [ExtTbl]

/-- Certificate check: order `N`, precision `K`, breakpoints `ds`, bounds `ql`, `qh`, products `ws`. -/
def quadBoundF (N K : Nat) (e : IExpr) (qa qb : Rat) (ds : List Rat) (ql qh : Rat)
    (ws : List FM) : Bool :=
  decide (ds.getLastD qa = qb) && Interval128.Dy.chainQ e qa ds &&
    match quadF moChk N K e qa ds ws with
    | some ((l, h), _) => decide (ql ≤ l) && decide (h ≤ qh)
    | none => false


/-- As `quadBoundF` without a certificate (products recomputed; for `native_decide`). -/
def quadBoundD (N K : Nat) (e : IExpr) (qa qb : Rat) (ds : List Rat) (ql qh : Rat) : Bool :=
  decide (ds.getLastD qa = qb) && Interval128.Dy.chainQ e qa ds &&
    match quadF moDir N K e qa ds [] with
    | some ((l, h), _) => decide (ql ≤ l) && decide (h ≤ qh)
    | none => false

end Interval128.F

/-! ### Soundness -/

noncomputable section

namespace RealFP.TMF

open Interval128.F RealFP.TMQ RealFP.I128Q

/-- Real coefficients `zᵢ / σ`. -/
def cl (σ : ℝ) (l : List ℤ) : List ℝ := l.map fun z : ℤ => (z : ℝ) / σ

@[simp] theorem cl_nil (σ : ℝ) : cl σ [] = [] := rfl
@[simp] theorem cl_cons (σ : ℝ) (a : ℤ) (l : List ℤ) : cl σ (a :: l) = ((a : ℝ) / σ) :: cl σ l := rfl

theorem cl_take (σ : ℝ) (n : ℕ) (l : List ℤ) : cl σ (l.take n) = (cl σ l).take n := by
  unfold cl; rw [List.map_take]

theorem cl_drop (σ : ℝ) (n : ℕ) (l : List ℤ) : cl σ (l.drop n) = (cl σ l).drop n := by
  unfold cl; rw [List.map_drop]

theorem pv_cl_addL (σ : ℝ) : ∀ (p q : List ℤ) (x : ℝ),
    pv (cl σ (addL p q)) x = pv (cl σ p) x + pv (cl σ q) x
  | [], q, x => by simp [addL, pv]
  | a :: p, [], x => by simp [addL, pv]
  | a :: p, b :: q, x => by
    simp only [addL, cl_cons, pv]; rw [pv_cl_addL σ p q x]; push_cast; ring

theorem pv_cl_map_mul (a : ℤ) (σ τ : ℝ) : ∀ (q : List ℤ) (x : ℝ),
    pv (cl (σ * τ) (q.map (a * ·))) x = ((a : ℝ) / σ) * pv (cl τ q) x
  | [], x => by simp [pv]
  | b :: q, x => by
    simp only [List.map_cons, cl_cons, pv]; rw [pv_cl_map_mul a σ τ q x]; push_cast; ring

theorem pv_cl_mulL (σ τ : ℝ) : ∀ (p q : List ℤ) (x : ℝ),
    pv (cl (σ * τ) (mulL p q)) x = pv (cl σ p) x * pv (cl τ q) x
  | [], q, x => by simp [mulL, pv]
  | a :: p, q, x => by
    simp only [mulL]
    rw [pv_cl_addL, pv_cl_map_mul]
    simp only [cl_cons, pv]
    rw [pv_cl_mulL σ τ p q x]; push_cast; ring

theorem pv_cl_neg (σ : ℝ) : ∀ (q : List ℤ) (x : ℝ), pv (cl σ (q.map (- ·))) x = - pv (cl σ q) x
  | [], x => by simp [pv]
  | b :: q, x => by
    simp only [List.map_cons, cl_cons, pv]; rw [pv_cl_neg σ q x]; push_cast; ring

theorem pv_cl_divmod (S : ℤ) (hS : (S : ℝ) ≠ 0) : ∀ (l : List ℤ) (x : ℝ),
    pv (cl ((S : ℝ) * S) l) x = pv (cl (S : ℝ) (l.map (· / S))) x + pv (cl ((S : ℝ) * S) (l.map (· % S))) x
  | [], x => by simp [pv]
  | z :: l, x => by
    simp only [List.map_cons, cl_cons, pv]
    rw [pv_cl_divmod S hS l x]
    have hz : (z : ℝ) = (S : ℝ) * ((z / S : ℤ) : ℝ) + ((z % S : ℤ) : ℝ) := by
      exact_mod_cast (Int.mul_ediv_add_emod z S).symm
    rw [hz]; field_simp; ring

/-! Rounding -/

theorem cdiv_ge (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ cdiv a b := by
  have h : a ≤ cdiv a b * b := by
    unfold cdiv
    have e := Nat.div_add_mod (a + b - 1) b
    have r := Nat.mod_lt (a + b - 1) hb
    generalize (a + b - 1) / b = q at *
    generalize (a + b - 1) % b = rr at *
    rw [Nat.mul_comm] at e
    omega
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast h

theorem floorQ_spec (q : ℚ) : (floorQ q : ℚ) ≤ q ∧ q < floorQ q + 1 := by
  have hd : (0 : ℚ) < q.den := by exact_mod_cast q.pos
  have e := Int.mul_ediv_add_emod q.num q.den
  have r0 := Int.emod_nonneg q.num (by exact_mod_cast q.den_nz : (q.den : ℤ) ≠ 0)
  have r1 := Int.emod_lt_of_pos q.num (by exact_mod_cast q.pos : (0 : ℤ) < q.den)
  unfold floorQ
  generalize q.num / (q.den : ℤ) = fl at *
  generalize q.num % (q.den : ℤ) = rr at *
  have hq : q = (q.num : ℚ) / q.den := (Rat.num_div_den q).symm
  constructor
  · conv_rhs => rw [hq]
    rw [le_div_iff₀ hd]
    have : fl * q.den ≤ q.num := by linarith [mul_comm (q.den : ℤ) fl]
    exact_mod_cast this
  · conv_lhs => rw [hq]
    rw [div_lt_iff₀ hd]
    have : q.num < (fl + 1) * q.den := by linarith [mul_comm (q.den : ℤ) fl]
    exact_mod_cast this

theorem floorQ_real (q : ℚ) : ((floorQ q : ℤ) : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (floorQ q : ℝ) + 1 := by
  have h := floorQ_spec q
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

theorem ceilQ_ge (q : ℚ) : (q : ℝ) ≤ ((ceilQ q).toNat : ℝ) := by
  have h := (floorQ_real (-q)).1
  have h2 : (ceilQ q : ℤ) ≤ ((ceilQ q).toNat : ℤ) := Int.self_le_toNat _
  have h3 : ((ceilQ q : ℤ) : ℝ) ≤ (((ceilQ q).toNat : ℤ) : ℝ) := by exact_mod_cast h2
  have h4 : (q : ℝ) ≤ ((ceilQ q : ℤ) : ℝ) := by
    unfold ceilQ; push_cast at h ⊢; linarith
  calc (q : ℝ) ≤ _ := h4
    _ ≤ _ := h3
    _ = _ := by norm_cast

theorem le_ceilN (K : ℕ) (q : ℚ) : (q : ℝ) ≤ ((ceilQ (q * 2 ^ K)).toNat : ℝ) / 2 ^ K := by
  rw [le_div_iff₀ (by positivity)]
  have := ceilQ_ge (q * 2 ^ K)
  push_cast at this; exact this

theorem floorN_bounds (K : ℕ) (q : ℚ) :
    ((floorQ (q * 2 ^ K) : ℤ) : ℝ) / 2 ^ K ≤ q ∧ (q : ℝ) - ((floorQ (q * 2 ^ K) : ℤ) : ℝ) / 2 ^ K < 1 / 2 ^ K := by
  have h := floorQ_real (q * 2 ^ K)
  push_cast at h
  have hs : (0 : ℝ) < 2 ^ K := by positivity
  constructor
  · rw [div_le_iff₀ hs]; linarith
  · rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hs]; linarith

/-! Models -/

variable (C : Cell) {lo hi : ℝ}

theorem pw_le {τ : ℝ} (hτ : |τ| ≤ (C.hn : ℝ) / 2 ^ C.K) (k : ℕ) :
    |τ| ^ k ≤ (pw C k : ℝ) / 2 ^ C.K := by
  have hs : (0 : ℝ) < 2 ^ C.K := by positivity
  have h1 : |τ| ^ k ≤ ((C.hn : ℝ) / 2 ^ C.K) ^ k := pow_le_pow_left₀ (abs_nonneg _) hτ k
  have h2 := cdiv_ge (C.hn ^ k * 2 ^ C.K) (2 ^ (C.K * k)) (by positivity)
  unfold pw
  refine le_trans h1 ?_
  rw [le_div_iff₀ hs]
  refine le_trans (le_of_eq ?_) h2
  push_cast
  rw [div_pow, pow_mul]
  field_simp

theorem adot_le {τ σ : ℝ} (hσ : 0 < σ) (hτ : |τ| ≤ (C.hn : ℝ) / 2 ^ C.K) :
    ∀ (l : List ℤ) (k : ℕ), |τ| ^ k * |pv (cl σ l) τ| ≤ (adot C l k : ℝ) / (σ * 2 ^ C.K)
  | [], k => by simp [pv, adot]
  | a :: l, k => by
    have ih := adot_le hσ hτ l (k + 1)
    have hp := pw_le C hτ k
    have hs : (0 : ℝ) < 2 ^ C.K := by positivity
    simp only [cl_cons, pv, adot]
    have e1 : |τ| ^ k * |(a : ℝ) / σ + τ * pv (cl σ l) τ| ≤
        |τ| ^ k * (|(a : ℝ)| / σ) + |τ| ^ (k + 1) * |pv (cl σ l) τ| := by
      have := abs_add_le ((a : ℝ) / σ) (τ * pv (cl σ l) τ)
      rw [abs_div, abs_of_pos hσ, abs_mul] at this
      have := mul_le_mul_of_nonneg_left this (pow_nonneg (abs_nonneg τ) k)
      rw [pow_succ]; nlinarith [pow_nonneg (abs_nonneg τ) k]
    have e2 : |τ| ^ k * (|(a : ℝ)| / σ) ≤ (pw C k : ℝ) / 2 ^ C.K * (|(a : ℝ)| / σ) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    refine le_trans e1 (le_trans (add_le_add e2 ih) (le_of_eq ?_))
    push_cast [Nat.cast_natAbs, Int.cast_abs]
    field_simp

/-- `A` encloses `f` on `[lo, hi]` (fixed point, centre `C.m`). -/
def FMok (f : ℝ → ℝ) (A : FM) : Prop :=
  ∀ t, lo ≤ t → t ≤ hi → |f t - pv (cl (2 ^ C.K) A.c) (t - C.m)| ≤ (A.r : ℝ) / 2 ^ C.K

variable {C}

theorem FMok.congr {f g : ℝ → ℝ} {A : FM} (h : FMok C (lo := lo) (hi := hi) f A)
    (hfg : ∀ t, lo ≤ t → t ≤ hi → f t = g t) : FMok C (lo := lo) (hi := hi) g A :=
  fun t h1 h2 => hfg t h1 h2 ▸ h t h1 h2

theorem ok_constQ (q : ℚ) : FMok C (lo := lo) (hi := hi) (fun _ => (q : ℝ)) (constQ C q) := by
  intro t _ _
  have h := floorN_bounds C.K q
  simp only [constQ, cl_cons, cl_nil, pv]
  rw [mul_zero, add_zero, abs_le]; push_cast
  constructor <;> linarith [h.1, h.2]

theorem ok_constDI {X : DI} {x : ℝ} (hx : mem x X) {A : FM} (h : constDI C X = some A) :
    FMok C (lo := lo) (hi := hi) (fun _ => x) A := by
  unfold constDI at h
  split at h
  · rename_i a b ha hb
    cases h
    intro t _ _
    have h1 := hx.1 a ha
    have h2 := hx.2 b hb
    rw [← toRat_val] at h1 h2
    set qa := Interval128.Dy.toRat a
    set qb := Interval128.Dy.toRat b
    have hf := floorN_bounds C.K ((qa + qb) / 2)
    have hc := le_ceilN C.K ((qb - qa) / 2)
    simp only [cl_cons, cl_nil, pv, mul_zero, add_zero]
    push_cast at hf hc ⊢
    rw [abs_le, add_div]
    have hs : (0 : ℝ) < 2 ^ C.K := by positivity
    have : (1 : ℝ) / 2 ^ C.K = 1 / 2 ^ C.K := rfl
    constructor <;> nlinarith [hf.1, hf.2, hc]
  · simp at h

theorem ok_var : FMok C (lo := lo) (hi := hi) (fun t => t) (var C) := by
  intro t _ _
  have h := floorN_bounds C.K C.m
  have hs : (2 : ℝ) ^ C.K ≠ 0 := by positivity
  simp only [var, cl_cons, cl_nil, pv, mul_zero, add_zero]
  push_cast
  rw [div_self hs, mul_one, abs_le]
  constructor <;> linarith [h.1, h.2]

theorem ok_add {f g : ℝ → ℝ} {A B : FM} (hf : FMok C (lo := lo) (hi := hi) f A)
    (hg : FMok C (lo := lo) (hi := hi) g B) :
    FMok C (lo := lo) (hi := hi) (fun t => f t + g t) (FM.add A B) := by
  intro t h1 h2
  have := abs_add_le (f t - pv (cl (2 ^ C.K) A.c) (t - C.m)) (g t - pv (cl (2 ^ C.K) B.c) (t - C.m))
  simp only [FM.add]
  rw [pv_cl_addL]; push_cast; rw [add_div]
  refine le_trans (le_of_eq ?_) (le_trans this (add_le_add (hf t h1 h2) (hg t h1 h2)))
  congr 1; ring

theorem ok_neg {f : ℝ → ℝ} {A : FM} (hf : FMok C (lo := lo) (hi := hi) f A) :
    FMok C (lo := lo) (hi := hi) (fun t => -f t) (FM.neg A) := by
  intro t h1 h2
  simp only [FM.neg]
  rw [pv_cl_neg, show -f t - -pv (cl (2 ^ C.K) A.c) (t - C.m) = -(f t - pv (cl (2 ^ C.K) A.c) (t - C.m)) by ring,
    abs_neg]
  exact hf t h1 h2

theorem ok_sub {f g : ℝ → ℝ} {A B : FM} (hf : FMok C (lo := lo) (hi := hi) f A)
    (hg : FMok C (lo := lo) (hi := hi) g B) :
    FMok C (lo := lo) (hi := hi) (fun t => f t - g t) (FM.sub A B) :=
  (ok_add hf (ok_neg hg)).congr fun t _ _ => by ring

theorem ok_addR {f g : ℝ → ℝ} {A : FM} {n : ℕ} (hg : FMok C (lo := lo) (hi := hi) g A)
    (hX : ∀ t, lo ≤ t → t ≤ hi → |f t - g t| ≤ (n : ℝ) / 2 ^ C.K) :
    FMok C (lo := lo) (hi := hi) f (A.addR n) := by
  intro t h1 h2
  have e : f t - pv (cl (2 ^ C.K) A.c) (t - C.m) =
      (f t - g t) + (g t - pv (cl (2 ^ C.K) A.c) (t - C.m)) := by ring
  simp only [FM.addR]; rw [e]; push_cast; rw [add_div]
  linarith [abs_add_le (f t - g t) (g t - pv (cl (2 ^ C.K) A.c) (t - C.m)), hX t h1 h2, hg t h1 h2]

variable (hC : ∀ t, lo ≤ t → t ≤ hi → |t - (C.m : ℝ)| ≤ (C.hn : ℝ) / 2 ^ C.K)
include hC

theorem ok_mul {f g : ℝ → ℝ} {A B : FM} (hf : FMok C (lo := lo) (hi := hi) f A)
    (hg : FMok C (lo := lo) (hi := hi) g B) :
    FMok C (lo := lo) (hi := hi) (fun t => f t * g t) (FM.mul C A B) := by
  intro t h1 h2
  have hτ := hC t h1 h2
  have hs : (0 : ℝ) < 2 ^ C.K := by positivity
  set s : ℝ := 2 ^ C.K with hs_def
  set τ := t - (C.m : ℝ)
  set d := mulL A.c B.c
  have hS : ((2 ^ C.K : ℤ) : ℝ) = s := by push_cast; rfl
  set a := pv (cl s A.c) τ
  set b := pv (cl s B.c) τ
  have hab : pv (cl (s * s) d) τ = a * b := pv_cl_mulL s s _ _ τ
  have hsplit := pv_take_drop C.N (cl (s * s) d) τ
  rw [← cl_take, ← cl_drop] at hsplit
  have hdm := pv_cl_divmod (2 ^ C.K) (by rw [hS]; exact hs.ne') (d.take C.N) τ
  rw [hS] at hdm
  have b1 := adot_le C (σ := s * s) (by positivity) hτ ((d.take C.N).map (· % (2 ^ C.K : ℤ))) 0
  have b2 := adot_le C (σ := s * s) (by positivity) hτ (d.drop C.N) C.N
  have b3 := adot_le C (σ := s) hs hτ A.c 0
  have b4 := adot_le C (σ := s) hs hτ B.c 0
  simp only [pow_zero, one_mul] at b1 b3 b4
  rw [← hs_def] at b1 b2 b3 b4
  have ef := hf t h1 h2
  have eg := hg t h1 h2
  set μ := adot C ((d.take C.N).map (· % (2 ^ C.K : ℤ))) 0
  set δ := adot C (d.drop C.N) C.N
  set α := adot C A.c 0
  set β := adot C B.c 0
  have c1 := cdiv_ge (μ + δ + α * B.r + β * A.r) (2 ^ C.K * 2 ^ C.K) (by positivity)
  have c2 := cdiv_ge (A.r * B.r) (2 ^ C.K) (by positivity)
  push_cast at c1 c2
  rw [← hs_def] at c1 c2
  show |f t * g t - pv (cl s ((d.take C.N).map (· / (2 ^ C.K : ℤ)))) τ| ≤
    ((cdiv (μ + δ + α * B.r + β * A.r) (2 ^ C.K * 2 ^ C.K) + cdiv (A.r * B.r) (2 ^ C.K) : ℕ) : ℝ) / s
  set X := f t - a
  set Y := g t - b
  set D := pv (cl (s * s) (d.drop C.N)) τ
  set M := pv (cl (s * s) ((d.take C.N).map (· % (2 ^ C.K : ℤ)))) τ
  have key : f t * g t - pv (cl s ((d.take C.N).map (· / (2 ^ C.K : ℤ)))) τ =
      X * Y + a * Y + b * X + τ ^ C.N * D + M := by
    have : f t * g t = (X + a) * (Y + b) := by simp only [X, Y]; ring
    rw [this]; linear_combination (-1 : ℝ) * hab + hsplit + hdm
  rw [key]
  have hX : |X| ≤ A.r / s := ef
  have hY : |Y| ≤ B.r / s := eg
  have hXY : |X * Y| ≤ A.r / s * (B.r / s) := by
    rw [abs_mul]; exact mul_le_mul hX hY (abs_nonneg _) (by positivity)
  have haY : |a * Y| ≤ α / (s * s) * (B.r / s) := by
    rw [abs_mul]; exact mul_le_mul b3 hY (abs_nonneg _) (by positivity)
  have hbX : |b * X| ≤ β / (s * s) * (A.r / s) := by
    rw [abs_mul]; exact mul_le_mul b4 hX (abs_nonneg _) (by positivity)
  have hD : |τ ^ C.N * D| ≤ δ / (s * s * s) := by rw [abs_mul, abs_pow]; exact b2
  have hM : |M| ≤ μ / (s * s * s) := b1
  have tri : |X * Y + a * Y + b * X + τ ^ C.N * D + M| ≤
      |X * Y| + |a * Y| + |b * X| + |τ ^ C.N * D| + |M| := by
    refine le_trans (abs_add_le _ _) (add_le_add ?_ le_rfl)
    refine le_trans (abs_add_le _ _) (add_le_add ?_ le_rfl)
    refine le_trans (abs_add_le _ _) (add_le_add ?_ le_rfl)
    exact abs_add_le _ _
  refine le_trans tri ?_
  have e1 : ((μ : ℝ) + δ + α * B.r + β * A.r) / (s * s) / s =
      μ / (s * s * s) + δ / (s * s * s) + α / (s * s) * (B.r / s) + β / (s * s) * (A.r / s) := by
    field_simp
  have e2 : (A.r : ℝ) * B.r / s / s = A.r / s * (B.r / s) := by field_simp
  have c1' := div_le_div_of_nonneg_right c1 hs.le
  have c2' := div_le_div_of_nonneg_right c2 hs.le
  rw [e1] at c1'; rw [e2] at c2'
  push_cast at c1' c2' ⊢
  rw [add_div]
  linarith

omit hC in
theorem ok_zero : FMok C (lo := lo) (hi := hi) (fun _ => 0) ⟨[], 0⟩ := by
  intro t _ _; simp [pv]

omit hC in
/-- Splitting off the centre value `p₀ = c₀ / 2^K`. -/
theorem ok_tail {f : ℝ → ℝ} {A : FM} (hf : FMok C (lo := lo) (hi := hi) f A) :
    FMok C (lo := lo) (hi := hi) (fun t => f t - (head C A : ℝ)) A.tail := by
  intro t h1 h2
  have := hf t h1 h2
  have e : pv (cl (2 ^ C.K) A.c) (t - C.m) =
      ((head C A : ℚ) : ℝ) + pv (cl (2 ^ C.K) A.tail.c) (t - C.m) := by
    unfold head FM.tail
    cases A.c <;> simp [pv]
  rw [e] at this
  refine le_trans (le_of_eq ?_) this
  congr 1; ring

omit hC in
theorem mag_le {g : ℝ → ℝ} {G : FM} (hg : FMok C (lo := lo) (hi := hi) g G)
    (hτ : ∀ t, lo ≤ t → t ≤ hi → |t - (C.m : ℝ)| ≤ (C.hn : ℝ) / 2 ^ C.K) :
    ∀ t, lo ≤ t → t ≤ hi → |g t| ≤ (magF C G : ℝ) := by
  intro t h1 h2
  have hs : (0 : ℝ) < 2 ^ C.K := by positivity
  have b := adot_le C (σ := 2 ^ C.K) hs (hτ t h1 h2) G.c 0
  simp only [pow_zero, one_mul] at b
  have c := cdiv_ge (adot C G.c 0) (2 ^ C.K) (by positivity)
  have e := hg t h1 h2
  have tri := abs_sub_abs_le_abs_sub (g t) (pv (cl (2 ^ C.K) G.c) (t - C.m))
  unfold magF
  push_cast at c ⊢
  rw [add_div]
  have : (adot C G.c 0 : ℝ) / (2 ^ C.K * 2 ^ C.K) ≤ (cdiv (adot C G.c 0) (2 ^ C.K) : ℝ) / 2 ^ C.K := by
    rw [← div_div]; exact div_le_div_of_nonneg_right c hs.le
  linarith

omit hC in
theorem remN_ge (q : ℚ) : (q : ℝ) ≤ (remN C q : ℝ) / 2 ^ C.K := le_ceilN C.K q

/-! Oracles -/

/-- The oracle returns true products. -/
def MoOK (mo : MO) : Prop :=
  ∀ C A B ws W ws', mo C A B ws = some (W, ws') → W = FM.mul C A B

omit hC in
theorem moChk_ok : MoOK moChk := by
  intro C A B ws W ws' h
  unfold moChk at h
  split at h
  · split at h
    · rename_i hW; cases h; exact hW
    · simp at h
  · simp at h

omit hC in
theorem moGen_ok : MoOK moGen := by
  intro C A B ws W ws' h; unfold moGen at h; cases h; rfl

omit hC in
theorem moDir_ok : MoOK moDir := by
  intro C A B ws W ws' h; unfold moDir at h; cases h; rfl

variable {mo : MO} (hmo : MoOK mo)
include hmo

theorem ok_mo {f g : ℝ → ℝ} {A B : FM} (hf : FMok C (lo := lo) (hi := hi) f A)
    (hg : FMok C (lo := lo) (hi := hi) g B) {ws W ws'} (h : mo C A B ws = some (W, ws')) :
    FMok C (lo := lo) (hi := hi) (fun t => f t * g t) W :=
  hmo _ _ _ _ _ _ h ▸ ok_mul hC hf hg

theorem ok_pow {f : ℝ → ℝ} {A : FM} (hf : FMok C (lo := lo) (hi := hi) f A) :
    ∀ n ws P ws', powF mo C A n ws = some (P, ws') → FMok C (lo := lo) (hi := hi) (fun t => f t ^ n) P
  | 0, ws, P, ws', h => by
    simp only [powF, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (ok_constQ 1).congr fun t _ _ => by simp
  | n + 1, ws, P, ws', h => by
    simp only [powF] at h
    rcases h1 : powF mo C A n ws with _ | ⟨P1, ws1⟩
    · rw [h1] at h; simp at h
    · rw [h1] at h
      exact (ok_mo hC hmo (ok_pow hf n ws P1 ws1 h1) hf h).congr fun t _ _ => by ring

theorem ok_ser {g : ℝ → ℝ} {G : FM} (hg : FMok C (lo := lo) (hi := hi) g G) :
    ∀ cs ws S ws', serF mo C G cs ws = some (S, ws') →
      FMok C (lo := lo) (hi := hi) (fun t => polyR cs (g t)) S
  | [], ws, S, ws', h => by
    simp only [serF, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ok_zero.congr fun t _ _ => by simp [polyR]
  | c :: cs, ws, S, ws', h => by
    simp only [serF] at h
    rcases h1 : serF mo C G cs ws with _ | ⟨S1, ws1⟩
    · rw [h1] at h; simp at h
    · rw [h1] at h
      simp only at h
      rcases h2 : mo C G S1 ws1 with _ | ⟨P, ws2⟩
      · rw [h2] at h; simp at h
      · rw [h2] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact (ok_add (ok_constQ c) (ok_mo hC hmo hg (ok_ser hg cs ws S1 ws1 h1) h2)).congr
          fun t _ _ => by simp [polyR]

theorem ok_exp {f : ℝ → ℝ} {A : FM} (hf : FMok C (lo := lo) (hi := hi) f A) {ws R ws'}
    (h : expF mo C A ws = some (R, ws')) :
    FMok C (lo := lo) (hi := hi) (fun t => Real.exp (f t)) R := by
  unfold expF at h
  dsimp only at h
  split_ifs at h with hr1
  rcases hE : constDI C (DI.exp (DI.ofRat (head C A))) with _ | E
  · rw [hE] at h; simp at h
  rw [hE] at h; simp only at h
  rcases hS : serF mo C A.tail (Interval128.Dy.coefs Interval128.Dy.expCoef 0 (C.N + 1)) ws with _ | ⟨S, ws1⟩
  · rw [hS] at h; simp at h
  rw [hS] at h; simp only at h
  have hg := ok_tail hf
  have hy : ∀ t, lo ≤ t → t ≤ hi → |f t - (head C A : ℝ)| ≤ (magF C A.tail : ℝ) := mag_le hg hC
  have hser := ok_ser hC hmo hg _ _ _ _ hS
  have hEx : FMok C (lo := lo) (hi := hi) (fun t => Real.exp (f t - (head C A : ℝ))) _ :=
    ok_addR hser fun t h1 h2 => by
      have hy1 : |f t - (head C A : ℝ)| ≤ 1 := le_trans (hy t h1 h2) (by exact_mod_cast hr1)
      rw [expCoef_sum]
      exact le_trans (Real.exp_bound hy1 (Nat.succ_pos C.N))
        (le_trans (rem_le (hy t h1 h2) _) (remN_ge _))
  have hE0 := ok_constDI (lo := lo) (hi := hi) (C := C) (mem_exp (mem_ofRat (head C A))) hE
  exact (ok_mo hC hmo hE0 hEx h).congr fun t _ _ => by rw [← Real.exp_add]; ring_nf

theorem ok_sinCos (cosQ : Bool) {f : ℝ → ℝ} {A : FM} (hf : FMok C (lo := lo) (hi := hi) f A)
    {ws R ws'} (h : sinCosF mo C cosQ A ws = some (R, ws')) :
    FMok C (lo := lo) (hi := hi) (fun t => scR cosQ (f t)) R := by
  unfold sinCosF at h
  dsimp only at h
  by_cases hr1 : magF C A.tail ≤ 1
  swap
  · simp [hr1] at h
  simp only [hr1, ↓reduceIte] at h
  rcases hS0 : constDI C (DI.sinCos false (DI.ofRat (head C A))) with _ | S0
  · rw [hS0] at h; simp at h
  rcases hC0 : constDI C (DI.sinCos true (DI.ofRat (head C A))) with _ | C0
  · rw [hS0, hC0] at h; simp at h
  rw [hS0, hC0] at h; simp only at h
  rcases hcg : serF mo C A.tail (Interval128.Dy.coefs Interval128.Dy.cosCoef 0 (C.N + 1)) ws with _ | ⟨cg, ws1⟩
  · rw [hcg] at h; simp at h
  rw [hcg] at h; simp only at h
  rcases hsg : serF mo C A.tail (Interval128.Dy.coefs Interval128.Dy.sinCoef 0 (C.N + 1)) ws1 with _ | ⟨sg, ws2⟩
  · rw [hsg] at h; simp at h
  rw [hsg] at h; simp only at h
  have hg := ok_tail hf
  have hy : ∀ t, lo ≤ t → t ≤ hi → |f t - (head C A : ℝ)| ≤ (magF C A.tail : ℝ) := mag_le hg hC
  have hy1 : ∀ t, lo ≤ t → t ≤ hi → |f t - (head C A : ℝ)| ≤ 1 := fun t h1 h2 =>
    le_trans (hy t h1 h2) (by exact_mod_cast hr1)
  have hCs : FMok C (lo := lo) (hi := hi) (fun t => Real.cos (f t - (head C A : ℝ))) _ :=
    ok_addR (ok_ser hC hmo hg _ _ _ _ hcg) fun t h1 h2 =>
      le_trans (cos_taylor_bound (hy1 t h1 h2) _ (Nat.succ_pos C.N))
        (le_trans (rem_le (hy t h1 h2) _) (remN_ge _))
  have hSn : FMok C (lo := lo) (hi := hi) (fun t => Real.sin (f t - (head C A : ℝ))) _ :=
    ok_addR (ok_ser hC hmo hg _ _ _ _ hsg) fun t h1 h2 =>
      le_trans (sin_taylor_bound (hy1 t h1 h2) _ (Nat.succ_pos C.N))
        (le_trans (rem_le (hy t h1 h2) _) (remN_ge _))
  have hs0 := ok_constDI (lo := lo) (hi := hi) (C := C) (I128Q.mem_sin (mem_ofRat (head C A))) hS0
  have hc0 := ok_constDI (lo := lo) (hi := hi) (C := C) (I128Q.mem_cos (mem_ofRat (head C A))) hC0
  cases cosQ
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    rcases hP : mo C S0 (cg.addR (remN C (Interval128.Dy.expRem (magF C A.tail) (C.N + 1)))) ws2 with _ | ⟨P, ws3⟩
    · rw [hP] at h; simp at h
    rw [hP] at h; simp only at h
    rcases hQ : mo C C0 (sg.addR (remN C (Interval128.Dy.expRem (magF C A.tail) (C.N + 1)))) ws3 with _ | ⟨Q, ws4⟩
    · rw [hQ] at h; simp at h
    rw [hQ] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (ok_add (ok_mo hC hmo hs0 hCs hP) (ok_mo hC hmo hc0 hSn hQ)).congr fun t _ _ => by
      simp only [scR, Bool.false_eq_true, ↓reduceIte]
      rw [show f t = (head C A : ℝ) + (f t - (head C A : ℝ)) by ring, Real.sin_add]; ring_nf
  · simp only [↓reduceIte] at h
    rcases hP : mo C C0 (cg.addR (remN C (Interval128.Dy.expRem (magF C A.tail) (C.N + 1)))) ws2 with _ | ⟨P, ws3⟩
    · rw [hP] at h; simp at h
    rw [hP] at h; simp only at h
    rcases hQ : mo C S0 (sg.addR (remN C (Interval128.Dy.expRem (magF C A.tail) (C.N + 1)))) ws3 with _ | ⟨Q, ws4⟩
    · rw [hQ] at h; simp at h
    rw [hQ] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (ok_sub (ok_mo hC hmo hc0 hCs hP) (ok_mo hC hmo hs0 hSn hQ)).congr fun t _ _ => by
      simp only [scR, ↓reduceIte]
      rw [show f t = (head C A : ℝ) + (f t - (head C A : ℝ)) by ring, Real.cos_add]; ring_nf

theorem ok_rel {f : ℝ → ℝ} {A : FM} (hf : FMok C (lo := lo) (hi := hi) f A) {ws I0 U r ws'}
    (h : relF mo C A ws = some ((I0, U, r), ws')) :
    (head C A : ℝ) ≠ 0 ∧ (r : ℝ) < 1 ∧
      FMok C (lo := lo) (hi := hi) (fun _ => ((head C A : ℝ))⁻¹) I0 ∧
      FMok C (lo := lo) (hi := hi) (fun t => (f t - (head C A : ℝ)) / (head C A : ℝ)) U ∧
      ∀ t, lo ≤ t → t ≤ hi → |(f t - (head C A : ℝ)) / (head C A : ℝ)| ≤ r := by
  unfold relF at h
  split_ifs at h with hnz
  rcases hI : constDI C (DI.inv (DI.ofRat (head C A))) with _ | I1
  · rw [hI] at h; simp at h
  rw [hI] at h; simp only at h
  rcases hU : mo C I1 A.tail ws with _ | ⟨U1, ws1⟩
  · rw [hU] at h; simp at h
  rw [hU] at h; simp only at h
  split_ifs at h with hr1
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
  have hne : (head C A : ℝ) ≠ 0 := by exact_mod_cast hnz
  have hi0 := ok_constDI (lo := lo) (hi := hi) (C := C) (I128Q.mem_inv (mem_ofRat (head C A))) hI
  have hu := (ok_mo hC hmo hi0 (ok_tail hf) hU).congr (g := fun t => (f t - (head C A : ℝ)) / (head C A : ℝ))
    fun t _ _ => by field_simp
  exact ⟨hne, by exact_mod_cast hr1, hi0, hu, mag_le hu hC⟩

theorem ok_inv {f : ℝ → ℝ} {A : FM} (hf : FMok C (lo := lo) (hi := hi) f A) {ws R ws'}
    (h : invF mo C A ws = some (R, ws')) :
    FMok C (lo := lo) (hi := hi) (fun t => (f t)⁻¹) R := by
  unfold invF at h
  rcases hr : relF mo C A ws with _ | ⟨⟨I0, U, r⟩, ws1⟩
  · rw [hr] at h; simp at h
  rw [hr] at h; simp only at h
  obtain ⟨hne, hr1, hi0, hU, hu⟩ := ok_rel hC hmo hf hr
  rcases hS : serF mo C U (Interval128.Dy.coefs Interval128.Dy.geoCoef 0 (C.N + 1)) ws1 with _ | ⟨S, ws2⟩
  · rw [hS] at h; simp at h
  rw [hS] at h; simp only at h
  have hS' : FMok C (lo := lo) (hi := hi) (fun t => (1 + (f t - (head C A : ℝ)) / (head C A : ℝ))⁻¹) _ :=
    ok_addR (ok_ser hC hmo hU _ _ _ _ hS) fun t h1 h2 => by
      rw [geoCoef_sum]
      refine le_trans (geo_bound (hu t h1 h2) hr1 (C.N + 1))
        (le_trans (le_of_eq ?_) (remN_ge (C := C) (r ^ (C.N + 1) / (1 - r))))
      push_cast; ring
  exact (ok_mo hC hmo hi0 hS' h).congr fun t _ _ => by
    rw [← mul_inv]; congr 1; field_simp; ring

theorem ok_log {f : ℝ → ℝ} {A : FM} (hf : FMok C (lo := lo) (hi := hi) f A) {ws R ws'}
    (h : logF mo C A ws = some (R, ws')) :
    FMok C (lo := lo) (hi := hi) (fun t => Real.log (f t)) R := by
  unfold logF at h
  split_ifs at h with hpos
  rcases hr : relF mo C A ws with _ | ⟨⟨I0, U, r⟩, ws1⟩
  · rw [hr] at h; simp at h
  rcases hY : DI.log? (DI.ofRat (head C A)) with _ | Y
  · rw [hr, hY] at h; simp at h
  rw [hr, hY] at h; simp only at h
  obtain ⟨hne, hr1, -, hU, hu⟩ := ok_rel hC hmo hf hr
  rcases hL : constDI C Y with _ | L
  · rw [hL] at h; simp at h
  rw [hL] at h; simp only at h
  rcases hS : serF mo C U (Interval128.Dy.coefs Interval128.Dy.lnCoef 0 (C.N + 2)) ws1 with _ | ⟨S, ws2⟩
  · rw [hS] at h; simp at h
  rw [hS] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hp : (0 : ℝ) < (head C A : ℝ) := by exact_mod_cast hpos
  have hl0 := ok_constDI (lo := lo) (hi := hi) (C := C) (mem_log? (mem_ofRat (head C A)) hY) hL
  have hS' : FMok C (lo := lo) (hi := hi) (fun t => Real.log (1 + (f t - (head C A : ℝ)) / (head C A : ℝ))) _ :=
    ok_addR (ok_ser hC hmo hU _ _ _ _ hS) fun t h1 h2 => by
      rw [lnCoef_sum]
      refine le_trans (log_bound (hu t h1 h2) hr1 (C.N + 1))
        (le_trans (le_of_eq ?_) (remN_ge (C := C) (r ^ (C.N + 2) / (1 - r))))
      push_cast; ring
  refine (ok_add hl0 hS').congr fun t h1 h2 => ?_
  have h1u : 0 < 1 + (f t - (head C A : ℝ)) / (head C A : ℝ) := by
    have := hu t h1 h2
    linarith [neg_abs_le ((f t - (head C A : ℝ)) / (head C A : ℝ))]
  rw [← Real.log_mul hne h1u.ne']; congr 1; field_simp; ring

set_option linter.concreteInstances false
variable [ExtTbl] [ExtSem]

theorem ok_tmF : ∀ (e : IExpr) {ws R ws'}, tmF mo C e ws = some (R, ws') →
    FMok C (lo := lo) (hi := hi) (fun t => e.denote [t]) R
  | .var i, ws, R, ws', h => by
    unfold tmF at h
    split_ifs at h with hi0
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    subst hi0
    exact ok_var.congr fun t _ _ => by simp [IExpr.denote]
  | .rat q, ws, R, ws', h => by
    unfold tmF at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (ok_constQ q).congr fun t _ _ => by simp [IExpr.denote]
  | .pi, ws, R, ws', h => by
    unfold tmF at h
    rcases hp : constDI C DI.pi with _ | P
    · rw [hp] at h; simp at h
    rw [hp] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (ok_constDI I128Q.mem_pi hp).congr fun t _ _ => by simp [IExpr.denote]
  | .add a b, ws, R, ws', h => by
    unfold tmF at h
    rcases ha : tmF mo C a ws with _ | ⟨A, ws1⟩
    · rw [ha] at h; simp at h
    rw [ha] at h; simp only at h
    rcases hb : tmF mo C b ws1 with _ | ⟨B, ws2⟩
    · rw [hb] at h; simp at h
    rw [hb] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (ok_add (ok_tmF a ha) (ok_tmF b hb)).congr fun t _ _ => by simp [IExpr.denote]
  | .sub a b, ws, R, ws', h => by
    unfold tmF at h
    rcases ha : tmF mo C a ws with _ | ⟨A, ws1⟩
    · rw [ha] at h; simp at h
    rw [ha] at h; simp only at h
    rcases hb : tmF mo C b ws1 with _ | ⟨B, ws2⟩
    · rw [hb] at h; simp at h
    rw [hb] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (ok_sub (ok_tmF a ha) (ok_tmF b hb)).congr fun t _ _ => by simp [IExpr.denote]
  | .mul a b, ws, R, ws', h => by
    unfold tmF at h
    rcases ha : tmF mo C a ws with _ | ⟨A, ws1⟩
    · rw [ha] at h; simp at h
    rw [ha] at h; simp only at h
    rcases hb : tmF mo C b ws1 with _ | ⟨B, ws2⟩
    · rw [hb] at h; simp at h
    rw [hb] at h; simp only at h
    exact (ok_mo hC hmo (ok_tmF a ha) (ok_tmF b hb) h).congr fun t _ _ => by simp [IExpr.denote]
  | .div a b, ws, R, ws', h => by
    unfold tmF at h
    rcases ha : tmF mo C a ws with _ | ⟨A, ws1⟩
    · rw [ha] at h; simp at h
    rw [ha] at h; simp only at h
    rcases hb : tmF mo C b ws1 with _ | ⟨B, ws2⟩
    · rw [hb] at h; simp at h
    rw [hb] at h; simp only at h
    rcases hi : invF mo C B ws2 with _ | ⟨IB, ws3⟩
    · rw [hi] at h; simp at h
    rw [hi] at h; simp only at h
    exact (ok_mo hC hmo (ok_tmF a ha) (ok_inv hC hmo (ok_tmF b hb) hi) h).congr fun t _ _ => by
      simp [IExpr.denote, div_eq_mul_inv]
  | .neg a, ws, R, ws', h => by
    unfold tmF at h
    rcases ha : tmF mo C a ws with _ | ⟨A, ws1⟩
    · rw [ha] at h; simp at h
    rw [ha] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (ok_neg (ok_tmF a ha)).congr fun t _ _ => by simp [IExpr.denote]
  | .inv a, ws, R, ws', h => by
    unfold tmF at h
    rcases ha : tmF mo C a ws with _ | ⟨A, ws1⟩
    · rw [ha] at h; simp at h
    rw [ha] at h; simp only at h
    exact (ok_inv hC hmo (ok_tmF a ha) h).congr fun t _ _ => by simp [IExpr.denote]
  | .pow a n, ws, R, ws', h => by
    unfold tmF at h
    rcases ha : tmF mo C a ws with _ | ⟨A, ws1⟩
    · rw [ha] at h; simp at h
    rw [ha] at h; simp only at h
    exact (ok_pow hC hmo (ok_tmF a ha) n _ _ _ h).congr fun t _ _ => by simp [IExpr.denote]
  | .exp a, ws, R, ws', h => by
    unfold tmF at h
    rcases ha : tmF mo C a ws with _ | ⟨A, ws1⟩
    · rw [ha] at h; simp at h
    rw [ha] at h; simp only at h
    exact (ok_exp hC hmo (ok_tmF a ha) h).congr fun t _ _ => by simp [IExpr.denote]
  | .log a, ws, R, ws', h => by
    unfold tmF at h
    rcases ha : tmF mo C a ws with _ | ⟨A, ws1⟩
    · rw [ha] at h; simp at h
    rw [ha] at h; simp only at h
    exact (ok_log hC hmo (ok_tmF a ha) h).congr fun t _ _ => by simp [IExpr.denote]
  | .sin a, ws, R, ws', h => by
    unfold tmF at h
    rcases ha : tmF mo C a ws with _ | ⟨A, ws1⟩
    · rw [ha] at h; simp at h
    rw [ha] at h; simp only at h
    exact (ok_sinCos hC hmo false (ok_tmF a ha) h).congr fun t _ _ => by simp [IExpr.denote, scR]
  | .cos a, ws, R, ws', h => by
    unfold tmF at h
    rcases ha : tmF mo C a ws with _ | ⟨A, ws1⟩
    · rw [ha] at h; simp at h
    rw [ha] at h; simp only at h
    exact (ok_sinCos hC hmo true (ok_tmF a ha) h).congr fun t _ _ => by simp [IExpr.denote, scR]
  | .sqrt _, _, _, _, h | .abs _, _, _, _, h | .atan _, _, _, _, h | .atan2 _ _, _, _, _, h
  | .sinh _, _, _, _, h | .cosh _, _, _, _, h | .tanh _, _, _, _, h | .log2 _, _, _, _, h
  | .log10 _, _, _, _, h | .tan _, _, _, _, h | .asin _, _, _, _, h | .acos _, _, _, _, h
  | .ext _ _ _, _, _, _, h => by unfold tmF at h; simp at h

end RealFP.TMF

namespace RealFP.TMF

open Interval128.F RealFP.TMQ RealFP.I128Q

/-! ### Integration -/

theorem int_cl (qa qb : ℚ) (σ : ℝ) : ∀ (l : List ℤ) (k : ℕ),
    ∫ x in (qa : ℝ)..qb, x ^ k * pv (cl σ l) x = (intQ qa qb k l : ℝ) / σ
  | [], k => by simp [pv, intQ]
  | c :: l, k => by
    simp only [intQ, cl_cons]
    have e : (fun x : ℝ => x ^ k * pv (((c : ℝ) / σ) :: cl σ l) x) =
        fun x => (c : ℝ) / σ * x ^ k + x ^ (k + 1) * pv (cl σ l) x := by
      funext x; simp only [pv]; ring
    have h1 : IntervalIntegrable (fun x : ℝ => (c : ℝ) / σ * x ^ k) MeasureTheory.volume (qa : ℝ) qb :=
      (continuous_const.mul (continuous_pow k)).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun x : ℝ => x ^ (k + 1) * pv (cl σ l) x) MeasureTheory.volume (qa : ℝ) qb :=
      ((continuous_pow (k + 1)).mul (continuous_pv _)).intervalIntegrable _ _
    rw [e, intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul, integral_pow,
      int_cl qa qb σ l (k + 1)]
    push_cast; ring

variable {mo : MO} (hmo : MoOK mo)
include hmo
set_option linter.concreteInstances false
variable [ExtTbl] [ExtSem]

theorem cell_ok {N K : ℕ} {e : IExpr} {lo hi : ℚ} {ws l h ws'} (hle : lo ≤ hi)
    (hd : Interval128.Dy.domOKQ (Interval128.Dy.boxes [(lo, hi)]) e = true)
    (hc : cellF mo N K e lo hi ws = some ((l, h), ws')) :
    IntervalIntegrable (fun t => e.denote [t]) MeasureTheory.volume (lo : ℝ) hi ∧
      (l : ℝ) ≤ ∫ t in (lo : ℝ)..hi, e.denote [t] ∧ ∫ t in (lo : ℝ)..hi, e.denote [t] ≤ h := by
  have hle' : (lo : ℝ) ≤ hi := by exact_mod_cast hle
  have hf : IntervalIntegrable (fun t => e.denote [t]) MeasureTheory.volume (lo : ℝ) hi :=
    (RealFP.I128Q.continuousOn_oneQ hd).intervalIntegrable_of_Icc hle'
  refine ⟨hf, ?_⟩
  unfold cellF at hc
  dsimp only at hc
  rcases ht : tmF mo (mkCell N K lo hi) e ws with _ | ⟨A, ws1⟩
  · rw [ht] at hc; simp at hc
  rw [ht] at hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hc
  set C := mkCell N K lo hi with hCdef
  have hm : C.m = (lo + hi) / 2 := rfl
  have hK : C.K = K := rfl
  have hC : ∀ t : ℝ, (lo : ℝ) ≤ t → t ≤ hi → |t - (C.m : ℝ)| ≤ (C.hn : ℝ) / 2 ^ C.K := by
    intro t h1 h2
    have := le_ceilN K ((hi - lo) / 2)
    rw [hm]; push_cast at this ⊢
    refine le_trans ?_ this
    rw [abs_le]; constructor <;> linarith
  have hA := ok_tmF hC hmo e ht
  set m : ℚ := C.m
  set s : ℝ := 2 ^ K
  have hs : (0 : ℝ) < s := by positivity
  have hpc : Continuous fun t : ℝ => pv (cl (2 ^ C.K) A.c) (t - m) :=
    (continuous_pv _).comp (continuous_sub_right _)
  have hpi := hpc.intervalIntegrable (μ := MeasureTheory.volume) (lo : ℝ) hi
  have hsplit : (∫ t in (lo : ℝ)..hi, e.denote [t]) =
      (∫ t in (lo : ℝ)..hi, pv (cl (2 ^ C.K) A.c) (t - m)) +
        ∫ t in (lo : ℝ)..hi, (e.denote [t] - pv (cl (2 ^ C.K) A.c) (t - m)) := by
    rw [intervalIntegral.integral_sub hf hpi]; ring
  have hP : (∫ t in (lo : ℝ)..hi, pv (cl (2 ^ C.K) A.c) (t - m)) =
      (intQ (lo - m) (hi - m) 0 A.c : ℝ) / s := by
    rw [intervalIntegral.integral_comp_sub_right (fun x => pv (cl (2 ^ C.K) A.c) x)]
    have := int_cl (lo - m) (hi - m) (2 ^ C.K) A.c 0
    simp only [pow_zero, one_mul] at this
    push_cast at this
    rw [this]; rfl
  have hR : |∫ t in (lo : ℝ)..hi, (e.denote [t] - pv (cl (2 ^ C.K) A.c) (t - m))| ≤
      (A.r : ℝ) / s * ((hi : ℝ) - lo) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (lo : ℝ)) (b := hi)
      (C := (A.r : ℝ) / s) (f := fun t => e.denote [t] - pv (cl (2 ^ C.K) A.c) (t - m))
      (fun t ht => by
        rw [Set.uIoc_of_le hle'] at ht
        rw [Real.norm_eq_abs]
        exact hA t ht.1.le ht.2)
    rw [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ (hi : ℝ) - lo by linarith)] at this
    exact this
  rw [hsplit, hP]
  have hb := abs_le.1 hR
  push_cast
  constructor <;> linarith [hb.1, hb.2]

theorem quad_ok {N K : ℕ} {e : IExpr} : ∀ (ds : List ℚ) (lo : ℚ) {ws l h ws'},
    quadF mo N K e lo ds ws = some ((l, h), ws') → Interval128.Dy.chainQ e lo ds = true →
    IntervalIntegrable (fun t => e.denote [t]) MeasureTheory.volume (lo : ℝ) (ds.getLastD lo) ∧
      (l : ℝ) ≤ ∫ t in (lo : ℝ)..(ds.getLastD lo : ℚ), e.denote [t] ∧
      ∫ t in (lo : ℝ)..(ds.getLastD lo : ℚ), e.denote [t] ≤ h
  | [], lo, ws, l, h, ws', hq, _ => by
    simp only [quadF, Option.some.injEq, Prod.mk.injEq] at hq
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hq
    simp
  | hi :: rest, lo, ws, l, h, ws', hq, hch => by
    simp only [Interval128.Dy.chainQ, Bool.and_eq_true, decide_eq_true_eq] at hch
    obtain ⟨⟨hle, hd⟩, hrest⟩ := hch
    simp only [quadF] at hq
    rcases h1 : cellF mo N K e lo hi ws with _ | ⟨⟨l1, h1'⟩, ws1⟩
    · rw [h1] at hq; simp at hq
    rw [h1] at hq; simp only at hq
    rcases h2 : quadF mo N K e hi rest ws1 with _ | ⟨⟨l2, h2'⟩, ws2⟩
    · rw [h2] at hq; simp at hq
    rw [h2] at hq; simp only [Option.some.injEq, Prod.mk.injEq] at hq
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hq
    have c := cell_ok hmo hle hd h1
    have r := quad_ok rest hi h2 hrest
    simp only [List.getLastD_cons]
    refine ⟨c.1.trans r.1, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals c.1 r.1]
    push_cast
    constructor <;> linarith [c.2.1, c.2.2, r.2.1, r.2.2]

omit hmo in
/-- **Rigorous integral bounds** from a fixed-point Taylor-model certificate (precision 128). -/
theorem integral_bounds_of_quadBoundF {N K : ℕ} {e : IExpr} {qa qb : ℚ} {ds : List ℚ}
    {ql qh : ℚ} {ws : List FM} (h : quadBoundF N K e qa qb ds ql qh ws = true) :
    (ql : ℝ) ≤ (∫ x in (qa : ℝ)..qb, e.denote [x]) ∧ (∫ x in (qa : ℝ)..qb, e.denote [x]) ≤ qh := by
  unfold quadBoundF at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hl, hc⟩, hq⟩ := h
  rcases hQ : quadF moChk N K e qa ds ws with _ | ⟨⟨l, h'⟩, ws'⟩
  · rw [hQ] at hq; simp at hq
  rw [hQ] at hq
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
  have := quad_ok moChk_ok ds qa hQ hc
  rw [hl] at this
  have h1 : (ql : ℝ) ≤ l := by exact_mod_cast hq.1
  have h2 : (h' : ℝ) ≤ qh := by exact_mod_cast hq.2
  exact ⟨h1.trans this.2.1, this.2.2.trans h2⟩

omit hmo in
/-- As `integral_bounds_of_quadBoundF`, for the uncertified check `quadBoundD`. -/
theorem integral_bounds_of_quadBoundD {N K : ℕ} {e : IExpr} {qa qb : ℚ} {ds : List ℚ}
    {ql qh : ℚ} (h : quadBoundD N K e qa qb ds ql qh = true) :
    (ql : ℝ) ≤ (∫ x in (qa : ℝ)..qb, e.denote [x]) ∧ (∫ x in (qa : ℝ)..qb, e.denote [x]) ≤ qh := by
  unfold quadBoundD at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hl, hc⟩, hq⟩ := h
  rcases hQ : quadF moDir N K e qa ds [] with _ | ⟨⟨l, h'⟩, ws'⟩
  · rw [hQ] at hq; simp at hq
  rw [hQ] at hq
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
  have := quad_ok moDir_ok ds qa hQ hc
  rw [hl] at this
  have h1 : (ql : ℝ) ≤ l := by exact_mod_cast hq.1
  have h2 : (h' : ℝ) ≤ qh := by exact_mod_cast hq.2
  exact ⟨h1.trans this.2.1, this.2.2.trans h2⟩

end RealFP.TMF
