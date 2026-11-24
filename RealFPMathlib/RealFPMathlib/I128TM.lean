/-
Taylor models at precision 128 and a kernel-checkable Taylor-model quadrature
(`integral_bound (precision := 128)`).

A Taylor model `⟨P, R⟩` (interval coefficients `P`, remainder interval `R`) encloses `f` on a cell
`[lo, hi]` with centre `m` if some real polynomial `p` with coefficients in `P` satisfies
`f t - p (t - m) ∈ R` for every `t` in the cell (`TMok`). Products are truncated (the dropped
part is bounded over the cell), and `exp`, `sin`, `cos`, `inv`, `log` are composed through
their Taylor series at the centre value with explicit remainders (`Real.exp_bound`,
`Complex.exp_bound`, the geometric series, `Real.abs_log_sub_add_sum_range_le`). The integral
of a cell is the exact integral of the polynomial part plus `R · (hi - lo)`.

Main result: `integral_bounds_of_quadBoundQ`.
-/
import RealFPMathlib.I128Roots

open Interval64 Interval64.KF
open Interval128.Dy (Dy DI)
open Finset

namespace Interval128.Dy

/-! ### Computable part -/

/-- Interval Taylor model: coefficients (in `t - m`) and remainder. -/
structure TM where
  P : List DI
  R : DI

def addP : List DI → List DI → List DI
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => DI.add a b :: addP p q

def mulP : List DI → List DI → List DI
  | [], _ => []
  | a :: p, q => addP (q.map (DI.mul a)) (DI.zero :: mulP p q)

/-- Horner range of `P` over `T`. -/
def rangeP (T : DI) : List DI → DI
  | [] => DI.zero
  | a :: p => DI.add a (DI.mul T (rangeP T p))

def TM.whole : TM := ⟨[], DI.whole⟩
def TM.const (C : DI) : TM := ⟨[C], DI.zero⟩
def TM.var (M : DI) : TM := ⟨[M, DI.ofRat 1], DI.zero⟩
def TM.add (A B : TM) : TM := ⟨addP A.P B.P, DI.add A.R B.R⟩
def TM.neg (A : TM) : TM := ⟨A.P.map DI.neg, DI.neg A.R⟩
def TM.sub (A B : TM) : TM := TM.add A B.neg
def TM.addR (A : TM) (X : DI) : TM := ⟨A.P, DI.add A.R X⟩

/-- Cell data: order `N`, offsets `T ∋ t - m`, `TN ∋ (t - m)^N` (computed once per cell). -/
structure Cell where
  N : Nat
  T : DI
  TN : DI

/-- Product, keeping `N` coefficients. -/
def TM.mul (C : Cell) (A B : TM) : TM :=
  let Cs := mulP A.P B.P
  ⟨Cs.take C.N, DI.add (DI.add (DI.mul C.TN (rangeP C.T (Cs.drop C.N)))
    (DI.mul (rangeP C.T A.P) B.R)) (DI.add (DI.mul (rangeP C.T B.P) A.R) (DI.mul A.R B.R))⟩

def TM.pow (C : Cell) (A : TM) : Nat → TM
  | 0 => TM.const (DI.ofRat 1)
  | n + 1 => TM.mul C (TM.pow C A n) A

/-- `Σ cₖ gᵏ` (Horner). -/
def TM.ser (C : Cell) (G : TM) : List Rat → TM
  | [] => TM.const DI.zero
  | c :: cs => TM.add (TM.const (DI.ofRat c)) (TM.mul C G (TM.ser C G cs))

/-- Centre coefficient and the rest. -/
def TM.head (A : TM) : DI := A.P.headD DI.zero
def TM.tail (A : TM) : TM := ⟨DI.zero :: A.P.tail, A.R⟩

/-- `max |lo| |hi|`. -/
def magQ (X : DI) : Option Rat :=
  match X.lo, X.hi with
  | some a, some b => some (Max.max |toRat a| |toRat b|)
  | _, _ => none

def expRem (r : Rat) (n : Nat) : Rat := r ^ n * ((n + 1 : Nat) : Rat) / ((fact n * n : Nat) : Rat)

def geoCoef (m : Nat) : Rat := (-1) ^ m
def lnCoef (m : Nat) : Rat := if m = 0 then 0 else (-1) ^ (m + 1) / (m : Rat)

def TM.exp (C : Cell) (A : TM) : TM :=
  let G := A.tail
  match magQ (DI.add (rangeP C.T G.P) G.R) with
  | some r =>
    if r ≤ 1 then
      TM.mul C (TM.const (DI.exp A.head))
        ((TM.ser C G (coefs expCoef 0 (C.N + 1))).addR (DI.pm (expRem r (C.N + 1))))
    else TM.whole
  | none => TM.whole

/-- `sin` (`cosQ = false`) or `cos`. -/
def TM.sinCos (cosQ : Bool) (C : Cell) (A : TM) : TM :=
  let G := A.tail
  match magQ (DI.add (rangeP C.T G.P) G.R) with
  | some r =>
    if r ≤ 1 then
      let S0 := TM.const (DI.sinCos false A.head)
      let C0 := TM.const (DI.sinCos true A.head)
      let b := DI.pm (expRem r (C.N + 1))
      let cg := (TM.ser C G (coefs cosCoef 0 (C.N + 1))).addR b
      let sg := (TM.ser C G (coefs sinCoef 0 (C.N + 1))).addR b
      if cosQ then TM.sub (TM.mul C C0 cg) (TM.mul C S0 sg)
      else TM.add (TM.mul C S0 cg) (TM.mul C C0 sg)
    else TM.whole
  | none => TM.whole

/-- `u = (f - p₀) / p₀` and a bound `|u| ≤ r < 1`. -/
def TM.rel (C : Cell) (A : TM) : Option (TM × Rat) :=
  if nzQ A.head then
    let G := A.tail
    let I0 := DI.inv A.head
    match magQ (DI.mul (DI.add (rangeP C.T G.P) G.R) I0) with
    | some r => if r < 1 then some (TM.mul C (TM.const I0) G, r) else none
    | none => none
  else none

def TM.inv (C : Cell) (A : TM) : TM :=
  match TM.rel C A with
  | some (U, r) =>
    TM.mul C (TM.const (DI.inv A.head))
      ((TM.ser C U (coefs geoCoef 0 (C.N + 1))).addR (DI.pm (r ^ (C.N + 1) / (1 - r))))
  | none => TM.whole

def TM.log (C : Cell) (A : TM) : TM :=
  if posQ A.head then
    match TM.rel C A, DI.log? A.head with
    | some (U, r), some Y =>
      TM.add (TM.const Y)
        ((TM.ser C U (coefs lnCoef 0 (C.N + 2))).addR (DI.pm (r ^ (C.N + 2) / (1 - r))))
    | _, _ => TM.whole
  else TM.whole

/-- Taylor model of `e` (variable `0`) on a cell with centre in `M`, offsets in `T`. -/
def tmE (C : Cell) (M : DI) : IExpr → TM
  | .var i => if i = 0 then TM.var M else TM.whole
  | .rat q => TM.const (DI.ofRat q)
  | .pi => TM.const DI.pi
  | .add a b => TM.add (tmE C M a) (tmE C M b)
  | .sub a b => TM.sub (tmE C M a) (tmE C M b)
  | .mul a b => TM.mul C (tmE C M a) (tmE C M b)
  | .div a b => TM.mul C (tmE C M a) (TM.inv C (tmE C M b))
  | .neg a => TM.neg (tmE C M a)
  | .inv a => TM.inv C (tmE C M a)
  | .pow a n => TM.pow C (tmE C M a) n
  | .exp a => TM.exp C (tmE C M a)
  | .log a => TM.log C (tmE C M a)
  | .sin a => TM.sinCos false C (tmE C M a)
  | .cos a => TM.sinCos true C (tmE C M a)
  | _ => TM.whole

/-- `∫_a^b τᵏ⁺ⁱ` weighted by the coefficients. -/
def intP (qa qb : Rat) : Nat → List DI → DI
  | _, [] => DI.zero
  | k, A :: P => DI.add (DI.mul A (DI.ofRat ((qb ^ (k + 1) - qa ^ (k + 1)) / (k + 1))))
      (intP qa qb (k + 1) P)

/-- Enclosure of `∫_lo^hi e` from one Taylor model of order `N` at the midpoint. -/
def cellQ (N : Nat) (e : IExpr) (lo hi : Rat) : DI :=
  let m := (lo + hi) / 2
  let T := DI.ofRatI (lo - m) (hi - m)
  let A := tmE ⟨N, T, DI.pow T N⟩ (DI.ofRat m) e
  DI.add (intP (lo - m) (hi - m) 0 A.P) (DI.mul A.R (DI.ofRat (hi - lo)))

set_option linter.concreteInstances false
variable [ExtTbl]

def quadQ (N : Nat) (e : IExpr) : Rat → List Rat → DI
  | _, [] => DI.zero
  | lo, hi :: rest => DI.add (cellQ N e lo hi) (quadQ N e hi rest)

/-- Cells are ordered and `e` is differentiable on each. -/
def chainQ (e : IExpr) : Rat → List Rat → Bool
  | _, [] => true
  | lo, hi :: rest => decide (lo ≤ hi) && domOKQ (boxes [(lo, hi)]) e && chainQ e hi rest

/-- Certificate: breakpoints `ds` (after `qa`, ending at `qb`), order `N`, bounds `ql`, `qh`. -/
def bndsQ (ql qh : Rat) (R : DI) : Bool := gGe ql R && gLe qh R

def quadBoundQ (N : Nat) (e : IExpr) (qa qb : Rat) (ds : List Rat) (ql qh : Rat) : Bool :=
  decide (ds.getLastD qa = qb) && chainQ e qa ds && bndsQ ql qh (quadQ N e qa ds)

end Interval128.Dy

/-! ### Soundness -/

noncomputable section

namespace RealFP.TMQ

open RealFP.I128Q
open Interval128.Dy (TM Cell addP mulP rangeP)

/-- Horner value `a₀ + x (a₁ + x (…))`. -/
def pv : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: p, x => a + x * pv p x

def addR : List ℝ → List ℝ → List ℝ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: addR p q

def mulR : List ℝ → List ℝ → List ℝ
  | [], _ => []
  | a :: p, q => addR (q.map (a * ·)) (0 :: mulR p q)

theorem pv_addR : ∀ (p q : List ℝ) (x : ℝ), pv (addR p q) x = pv p x + pv q x
  | [], q, x => by simp [addR, pv]
  | a :: p, [], x => by simp [addR, pv]
  | a :: p, b :: q, x => by simp only [addR, pv, pv_addR p q x]; ring

theorem pv_map_mul (a : ℝ) : ∀ (q : List ℝ) (x : ℝ), pv (q.map (a * ·)) x = a * pv q x
  | [], x => by simp [pv]
  | b :: q, x => by simp only [List.map_cons, pv, pv_map_mul a q x]; ring

theorem pv_map_neg : ∀ (q : List ℝ) (x : ℝ), pv (q.map (- ·)) x = - pv q x
  | [], x => by simp [pv]
  | b :: q, x => by simp only [List.map_cons, pv, pv_map_neg q x]; ring

theorem pv_mulR : ∀ (p q : List ℝ) (x : ℝ), pv (mulR p q) x = pv p x * pv q x
  | [], q, x => by simp [mulR, pv]
  | a :: p, q, x => by
    simp only [mulR, pv_addR, pv_map_mul, pv, pv_mulR p q x]; ring

theorem pv_take_drop : ∀ (n : ℕ) (l : List ℝ) (x : ℝ),
    pv l x = pv (l.take n) x + x ^ n * pv (l.drop n) x
  | 0, l, x => by simp [pv]
  | n + 1, [], x => by simp [pv]
  | n + 1, a :: l, x => by
    simp only [List.take_succ_cons, List.drop_succ_cons, pv]
    rw [pv_take_drop n l x]; ring

theorem pv_head_tail (p : List ℝ) (x : ℝ) : pv p x = p.headD 0 + pv (0 :: p.tail) x := by
  cases p <;> simp [pv]

theorem continuous_pv : ∀ p : List ℝ, Continuous (pv p)
  | [] => by simp only [pv]; exact continuous_const
  | a :: p => by
    show Continuous fun x => a + x * pv p x
    exact continuous_const.add (continuous_id.mul (continuous_pv p))

/-! Interval lists -/

theorem mem_addP : ∀ {p q : List ℝ} {P Q : List DI}, List.Forall₂ mem p P → List.Forall₂ mem q Q →
    List.Forall₂ mem (addR p q) (addP P Q)
  | [], _, [], _, .nil, hq => by simpa [addR, addP] using hq
  | _ :: _, [], _ :: _, [], .cons ha hp, .nil => by simpa [addR, addP] using List.Forall₂.cons ha hp
  | _ :: _, _ :: _, _ :: _, _ :: _, .cons ha hp, .cons hb hq => by
    simp only [addR, addP]; exact List.Forall₂.cons (I128Q.mem_add ha hb) (mem_addP hp hq)

theorem mem_map_mul {a : ℝ} {A : DI} (ha : mem a A) : ∀ {q : List ℝ} {Q : List DI},
    List.Forall₂ mem q Q → List.Forall₂ mem (q.map (a * ·)) (Q.map (DI.mul A))
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hb hq => List.Forall₂.cons (I128Q.mem_mul ha hb) (mem_map_mul ha hq)

theorem mem_map_neg : ∀ {q : List ℝ} {Q : List DI},
    List.Forall₂ mem q Q → List.Forall₂ mem (q.map (- ·)) (Q.map DI.neg)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hb hq => List.Forall₂.cons (I128Q.mem_neg hb) (mem_map_neg hq)

theorem mem_mulP : ∀ {p q : List ℝ} {P Q : List DI}, List.Forall₂ mem p P → List.Forall₂ mem q Q →
    List.Forall₂ mem (mulR p q) (mulP P Q)
  | [], _, [], _, .nil, _ => by simp only [mulR, mulP]; exact .nil
  | _ :: _, _, _ :: _, _, .cons ha hp, hq => by
    simp only [mulR, mulP]
    exact mem_addP (mem_map_mul ha hq) (List.Forall₂.cons mem_zeroD (mem_mulP hp hq))

theorem mem_take : ∀ (n : ℕ) {p : List ℝ} {P : List DI}, List.Forall₂ mem p P →
    List.Forall₂ mem (p.take n) (P.take n)
  | 0, _, _, _ => by simp
  | _ + 1, [], [], .nil => by simp
  | n + 1, _ :: _, _ :: _, .cons ha hp => by
    simp only [List.take_succ_cons]; exact List.Forall₂.cons ha (mem_take n hp)

theorem mem_drop : ∀ (n : ℕ) {p : List ℝ} {P : List DI}, List.Forall₂ mem p P →
    List.Forall₂ mem (p.drop n) (P.drop n)
  | 0, _, _, h => by simpa using h
  | _ + 1, [], [], .nil => by simp
  | n + 1, _ :: _, _ :: _, .cons _ hp => by simp only [List.drop_succ_cons]; exact mem_drop n hp

theorem mem_rangeP {T : DI} {x : ℝ} (hx : mem x T) : ∀ {p : List ℝ} {P : List DI},
    List.Forall₂ mem p P → mem (pv p x) (rangeP T P)
  | [], [], .nil => mem_zeroD
  | _ :: _, _ :: _, .cons ha hp => I128Q.mem_add ha (I128Q.mem_mul hx (mem_rangeP hx hp))

theorem mem_headD : ∀ {p : List ℝ} {P : List DI}, List.Forall₂ mem p P →
    mem (p.headD 0) (P.headD DI.zero)
  | [], [], .nil => mem_zeroD
  | _ :: _, _ :: _, .cons ha _ => ha

theorem mem_tail : ∀ {p : List ℝ} {P : List DI}, List.Forall₂ mem p P →
    List.Forall₂ mem p.tail P.tail
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons _ hp => hp

theorem magQ_le {X : DI} {x : ℝ} {r : ℚ} (hx : mem x X) (h : Interval128.Dy.magQ X = some r) :
    |x| ≤ r := by
  unfold Interval128.Dy.magQ at h
  split at h
  · rename_i a b ha hb
    cases Option.some.inj h
    have h1 := hx.1 a ha
    have h2 := hx.2 b hb
    rw [← toRat_val] at h1 h2
    push_cast
    refine abs_le.2 ⟨?_, ?_⟩
    · have : -((Interval128.Dy.toRat a : ℚ) : ℝ) ≤ |((Interval128.Dy.toRat a : ℚ) : ℝ)| := neg_le_abs _
      have h3 : |((Interval128.Dy.toRat a : ℚ) : ℝ)| ≤ max |((Interval128.Dy.toRat a : ℚ) : ℝ)|
        |((Interval128.Dy.toRat b : ℚ) : ℝ)| := le_max_left _ _
      linarith
    · have : ((Interval128.Dy.toRat b : ℚ) : ℝ) ≤ |((Interval128.Dy.toRat b : ℚ) : ℝ)| := le_abs_self _
      have h3 : |((Interval128.Dy.toRat b : ℚ) : ℝ)| ≤ max |((Interval128.Dy.toRat a : ℚ) : ℝ)|
        |((Interval128.Dy.toRat b : ℚ) : ℝ)| := le_max_right _ _
      linarith
  · simp at h

/-! ### Taylor models -/

theorem mem_of_eq {x y : ℝ} {X Y : DI} (h : mem x X) (hxy : x = y) (hXY : X = Y) : mem y Y :=
  hxy ▸ hXY ▸ h

/-- `A` encloses `f` on `[lo, hi]` around `m`. -/
def TMok (m lo hi : ℝ) (f : ℝ → ℝ) (A : TM) : Prop :=
  ∃ p : List ℝ, List.Forall₂ mem p A.P ∧ ∀ t, lo ≤ t → t ≤ hi → mem (f t - pv p (t - m)) A.R

variable {m lo hi : ℝ} {C : Cell}
  (hT : ∀ t, lo ≤ t → t ≤ hi → mem (t - m) C.T ∧ mem ((t - m) ^ C.N) C.TN)

theorem TMok.congr {f g : ℝ → ℝ} {A : TM} (h : TMok m lo hi f A)
    (hfg : ∀ t, lo ≤ t → t ≤ hi → f t = g t) : TMok m lo hi g A := by
  obtain ⟨p, hp, hr⟩ := h
  exact ⟨p, hp, fun t h1 h2 => hfg t h1 h2 ▸ hr t h1 h2⟩

theorem ok_whole (f : ℝ → ℝ) : TMok m lo hi f TM.whole :=
  ⟨[], .nil, fun _ _ _ => I128Q.mem_whole _⟩

theorem ok_const {c : ℝ} {C : DI} (hc : mem c C) : TMok m lo hi (fun _ => c) (TM.const C) :=
  ⟨[c], .cons hc .nil, fun _ _ _ => mem_of_eq mem_zeroD (by simp [pv]) rfl⟩

theorem ok_var {M : DI} (hM : mem m M) : TMok m lo hi (fun t => t) (TM.var M) :=
  ⟨[m, 1], .cons hM (.cons (mem_ofRat' 1 (by simp)) .nil),
    fun t _ _ => mem_of_eq mem_zeroD (by simp [pv]) rfl⟩

theorem ok_add {f g : ℝ → ℝ} {A B : TM} (hf : TMok m lo hi f A) (hg : TMok m lo hi g B) :
    TMok m lo hi (fun t => f t + g t) (TM.add A B) := by
  obtain ⟨p, hp, hr⟩ := hf
  obtain ⟨q, hq, hs⟩ := hg
  refine ⟨addR p q, mem_addP hp hq, fun t h1 h2 => ?_⟩
  have := I128Q.mem_add (hr t h1 h2) (hs t h1 h2)
  exact mem_of_eq this (by rw [pv_addR]; ring) rfl

theorem ok_neg {f : ℝ → ℝ} {A : TM} (hf : TMok m lo hi f A) :
    TMok m lo hi (fun t => -f t) (TM.neg A) := by
  obtain ⟨p, hp, hr⟩ := hf
  refine ⟨p.map (- ·), mem_map_neg hp, fun t h1 h2 => ?_⟩
  have := I128Q.mem_neg (hr t h1 h2)
  exact mem_of_eq this (by rw [pv_map_neg]; ring) rfl

theorem ok_sub {f g : ℝ → ℝ} {A B : TM} (hf : TMok m lo hi f A) (hg : TMok m lo hi g B) :
    TMok m lo hi (fun t => f t - g t) (TM.sub A B) :=
  (ok_add hf (ok_neg hg)).congr fun t _ _ => by ring

theorem ok_addR {f g : ℝ → ℝ} {A : TM} {X : DI} (hg : TMok m lo hi g A)
    (hX : ∀ t, lo ≤ t → t ≤ hi → mem (f t - g t) X) : TMok m lo hi f (A.addR X) := by
  obtain ⟨p, hp, hr⟩ := hg
  refine ⟨p, hp, fun t h1 h2 => ?_⟩
  exact mem_of_eq (I128Q.mem_add (hr t h1 h2) (hX t h1 h2)) (by ring) rfl

include hT in
theorem ok_mul {f g : ℝ → ℝ} {A B : TM} (hf : TMok m lo hi f A) (hg : TMok m lo hi g B) :
    TMok m lo hi (fun t => f t * g t) (TM.mul C A B) := by
  obtain ⟨p, hp, hr⟩ := hf
  obtain ⟨q, hq, hs⟩ := hg
  have hc := mem_mulP hp hq
  refine ⟨(mulR p q).take C.N, mem_take C.N hc, fun t h1 h2 => ?_⟩
  have ht := (hT t h1 h2).1
  have := I128Q.mem_add (I128Q.mem_add (I128Q.mem_mul (hT t h1 h2).2 (mem_rangeP ht (mem_drop C.N hc)))
    (I128Q.mem_mul (mem_rangeP ht hp) (hs t h1 h2)))
    (I128Q.mem_add (I128Q.mem_mul (mem_rangeP ht hq) (hr t h1 h2)) (I128Q.mem_mul (hr t h1 h2) (hs t h1 h2)))
  have e := pv_take_drop C.N (mulR p q) (t - m)
  rw [pv_mulR] at e
  exact mem_of_eq this (by linear_combination (-1 : ℝ) * e) rfl

include hT in
theorem ok_pow {f : ℝ → ℝ} {A : TM} (hf : TMok m lo hi f A) :
    ∀ n : ℕ, TMok m lo hi (fun t => f t ^ n) (TM.pow C A n)
  | 0 => (ok_const (c := (1 : ℝ)) (I128Q.mem_ofRat' 1 (by norm_num))).congr fun t _ _ => by simp
  | n + 1 => (ok_mul hT (ok_pow hf n) hf).congr fun t _ _ => by ring

include hT in
theorem ok_ser {g : ℝ → ℝ} {G : TM} (hg : TMok m lo hi g G) :
    ∀ cs : List ℚ, TMok m lo hi (fun t => polyR cs (g t)) (TM.ser C G cs)
  | [] => (ok_const mem_zeroD).congr fun t _ _ => by simp [polyR]
  | c :: cs => (ok_add (ok_const (I128Q.mem_ofRat c)) (ok_mul hT hg (ok_ser hg cs))).congr
      fun t _ _ => by simp [polyR]

/-- Splitting off the centre coefficient: `f = p₀ + g`, `g` with the tail model. -/
theorem ok_tail {f : ℝ → ℝ} {A : TM} (hf : TMok m lo hi f A) :
    ∃ p0 : ℝ, mem p0 A.head ∧ TMok m lo hi (fun t => f t - p0) A.tail := by
  obtain ⟨p, hp, hr⟩ := hf
  refine ⟨p.headD 0, mem_headD hp, 0 :: p.tail, List.Forall₂.cons mem_zeroD (mem_tail hp),
    fun t h1 h2 => ?_⟩
  have := hr t h1 h2
  rw [pv_head_tail p] at this
  exact mem_of_eq this (by ring) rfl

include hT in
/-- Range of a model over the cell. -/
theorem ok_range {g : ℝ → ℝ} {G : TM} (hg : TMok m lo hi g G) :
    ∀ t, lo ≤ t → t ≤ hi → mem (g t) (DI.add (rangeP C.T G.P) G.R) := by
  obtain ⟨p, hp, hr⟩ := hg
  intro t h1 h2
  exact mem_of_eq (I128Q.mem_add (mem_rangeP (hT t h1 h2).1 hp) (hr t h1 h2)) (by ring) rfl

theorem expRem_cast (r : ℚ) (n : ℕ) :
    ((Interval128.Dy.expRem r n : ℚ) : ℝ) = (r : ℝ) ^ n * ((n.succ : ℝ) / (n.factorial * n)) := by
  simp only [Interval128.Dy.expRem, fact_eq]; push_cast; ring

theorem rem_le {y : ℝ} {r : ℚ} (hy : |y| ≤ r) (n : ℕ) :
    |y| ^ n * ((n.succ : ℝ) / (n.factorial * n)) ≤ ((Interval128.Dy.expRem r n : ℚ) : ℝ) := by
  rw [expRem_cast]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hy _) (by positivity)

include hT in
theorem ok_exp {f : ℝ → ℝ} {A : TM} (hf : TMok m lo hi f A) :
    TMok m lo hi (fun t => Real.exp (f t)) (TM.exp C A) := by
  dsimp only [TM.exp]
  split
  · rename_i r hrm
    split
    · rename_i hr1
      obtain ⟨p0, hp0, hg⟩ := ok_tail hf
      have hrng := ok_range hT hg
      have hser := ok_ser hT hg (Interval128.Dy.coefs Interval128.Dy.expCoef 0 (C.N + 1))
      have hE : TMok m lo hi (fun t => Real.exp (f t - p0)) _ := ok_addR hser fun t h1 h2 => by
        have hy := magQ_le (hrng t h1 h2) hrm
        have hy1 : |f t - p0| ≤ 1 := le_trans hy (by exact_mod_cast hr1)
        apply mem_pm
        rw [expCoef_sum]
        exact le_trans (Real.exp_bound hy1 (Nat.succ_pos C.N)) (rem_le hy _)
      exact (ok_mul hT (ok_const (I128Q.mem_exp hp0)) hE).congr fun t _ _ => by
        rw [← Real.exp_add]; ring_nf
    · exact ok_whole _
  · exact ok_whole _

/-- `cos` (`true`) or `sin` (`false`). -/
def scR (cosQ : Bool) (x : ℝ) : ℝ := if cosQ then Real.cos x else Real.sin x

include hT in
theorem ok_sinCos (cosQ : Bool) {f : ℝ → ℝ} {A : TM} (hf : TMok m lo hi f A) :
    TMok m lo hi (fun t => scR cosQ (f t)) (TM.sinCos cosQ C A) := by
  dsimp only [TM.sinCos]
  split
  · rename_i r hrm
    split
    · rename_i hr1
      obtain ⟨p0, hp0, hg⟩ := ok_tail hf
      have hrng := ok_range hT hg
      have hy t (h1 : lo ≤ t) (h2 : t ≤ hi) : |f t - p0| ≤ r := magQ_le (hrng t h1 h2) hrm
      have hy1 t (h1 : lo ≤ t) (h2 : t ≤ hi) : |f t - p0| ≤ 1 :=
        le_trans (hy t h1 h2) (by exact_mod_cast hr1)
      have hC : TMok m lo hi (fun t => Real.cos (f t - p0)) _ :=
        ok_addR (X := DI.pm (Interval128.Dy.expRem r (C.N + 1)))
          (ok_ser hT hg (Interval128.Dy.coefs Interval128.Dy.cosCoef 0 (C.N + 1)))
          fun t h1 h2 => I128Q.mem_pm (le_trans (cos_taylor_bound (hy1 t h1 h2) _ (Nat.succ_pos C.N))
            (rem_le (hy t h1 h2) _))
      have hS : TMok m lo hi (fun t => Real.sin (f t - p0)) _ :=
        ok_addR (X := DI.pm (Interval128.Dy.expRem r (C.N + 1)))
          (ok_ser hT hg (Interval128.Dy.coefs Interval128.Dy.sinCoef 0 (C.N + 1)))
          fun t h1 h2 => I128Q.mem_pm (le_trans (sin_taylor_bound (hy1 t h1 h2) _ (Nat.succ_pos C.N))
            (rem_le (hy t h1 h2) _))
      cases cosQ
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact (ok_add (ok_mul hT (ok_const (I128Q.mem_sin hp0)) hC)
          (ok_mul hT (ok_const (I128Q.mem_cos hp0)) hS)).congr fun t _ _ => by
            simp only [scR, Bool.false_eq_true, ↓reduceIte]
            rw [show f t = p0 + (f t - p0) by ring, Real.sin_add]; ring_nf
      · simp only [↓reduceIte]
        exact (ok_sub (ok_mul hT (ok_const (I128Q.mem_cos hp0)) hC)
          (ok_mul hT (ok_const (I128Q.mem_sin hp0)) hS)).congr fun t _ _ => by
            simp only [scR, ↓reduceIte]
            rw [show f t = p0 + (f t - p0) by ring, Real.cos_add]; ring_nf
    · exact ok_whole _
  · exact ok_whole _

include hT in
theorem ok_rel {f : ℝ → ℝ} {A : TM} (hf : TMok m lo hi f A) {U : TM} {r : ℚ}
    (h : TM.rel C A = some (U, r)) :
    ∃ p0 : ℝ, mem p0 A.head ∧ p0 ≠ 0 ∧ r < 1 ∧
      TMok m lo hi (fun t => (f t - p0) / p0) U ∧
      ∀ t, lo ≤ t → t ≤ hi → |(f t - p0) / p0| ≤ r := by
  dsimp only [TM.rel] at h
  split at h
  · rename_i hnz
    split at h
    · rename_i r' hrm
      split at h
      · rename_i hr1
        cases h
        obtain ⟨p0, hp0, hg⟩ := ok_tail hf
        have hne := ne_of_nzQ hnz hp0
        refine ⟨p0, hp0, hne, by exact_mod_cast hr1,
          (ok_mul hT (ok_const (I128Q.mem_inv hp0)) hg).congr fun t _ _ => by field_simp, ?_⟩
        intro t h1 h2
        have := magQ_le (I128Q.mem_mul (ok_range hT hg t h1 h2) (I128Q.mem_inv hp0)) hrm
        simpa [div_eq_mul_inv] using this
      · simp at h
    · simp at h
  · simp at h

theorem geo_bound {u : ℝ} {r : ℝ} (hu : |u| ≤ r) (hr : r < 1) (n : ℕ) :
    |(1 + u)⁻¹ - ∑ i ∈ range n, (-u) ^ i| ≤ r ^ n / (1 - r) := by
  have h1 : 0 < 1 + u := by linarith [neg_abs_le u]
  have hne : -u ≠ 1 := by intro h; linarith
  have hr0 : 0 ≤ r := le_trans (abs_nonneg _) hu
  rw [geom_sum_eq hne]
  have e : (1 + u)⁻¹ - ((-u) ^ n - 1) / (-u - 1) = (-u) ^ n / (1 + u) := by
    rw [show -u - 1 = -(1 + u) by ring]
    field_simp
    ring
  rw [e, abs_div, abs_pow, abs_neg, abs_of_pos h1]
  have h2 : 1 - r ≤ 1 + u := by linarith [neg_abs_le u]
  have h3 : 0 < 1 - r := by linarith
  calc |u| ^ n / (1 + u) ≤ r ^ n / (1 + u) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hu _) h1.le
    _ ≤ r ^ n / (1 - r) := div_le_div_of_nonneg_left (pow_nonneg hr0 _) h3 h2

theorem geoCoef_sum (u : ℝ) (n : ℕ) :
    polyR (Interval128.Dy.coefs Interval128.Dy.geoCoef 0 n) u = ∑ i ∈ range n, (-u) ^ i := by
  rw [polyR_coefs]; apply sum_congr rfl; intro i _
  rw [neg_pow]; simp only [Interval128.Dy.geoCoef, zero_add]; push_cast; ring

include hT in
theorem ok_inv {f : ℝ → ℝ} {A : TM} (hf : TMok m lo hi f A) :
    TMok m lo hi (fun t => (f t)⁻¹) (TM.inv C A) := by
  dsimp only [TM.inv]
  split
  · rename_i U r hrel
    obtain ⟨p0, hp0, hne, hr1, hU, hu⟩ := ok_rel hT hf hrel
    have hS : TMok m lo hi (fun t => (1 + (f t - p0) / p0)⁻¹) _ :=
      ok_addR (X := DI.pm (r ^ (C.N + 1) / (1 - r))) (ok_ser hT hU (Interval128.Dy.coefs Interval128.Dy.geoCoef 0 (C.N + 1)))
        fun t h1 h2 => by
          apply mem_pm; rw [geoCoef_sum]
          have := geo_bound (hu t h1 h2) (by exact_mod_cast hr1) (C.N + 1)
          push_cast; exact this
    exact (ok_mul hT (ok_const (I128Q.mem_inv hp0)) hS).congr fun t _ _ => by
      rw [← mul_inv]; congr 1; field_simp; ring
  · exact ok_whole _

theorem lnCoef_sum (u : ℝ) (n : ℕ) :
    polyR (Interval128.Dy.coefs Interval128.Dy.lnCoef 0 (n + 1)) u =
      -∑ i ∈ range n, (-u) ^ (i + 1) / (i + 1) := by
  rw [polyR_coefs, sum_range_succ', ← sum_neg_distrib]
  simp only [Interval128.Dy.lnCoef, zero_add, ite_true, Rat.cast_zero, zero_mul, add_zero]
  apply sum_congr rfl; intro i _
  simp only [Nat.add_one_ne_zero, ite_false]; push_cast
  rw [neg_pow, show (-1 : ℝ) ^ (i + 1 + 1) = (-1) ^ (i + 1) * (-1) by ring]
  ring

theorem log_bound {u : ℝ} {r : ℝ} (hu : |u| ≤ r) (hr : r < 1) (n : ℕ) :
    |Real.log (1 + u) - -∑ i ∈ range n, (-u) ^ (i + 1) / (i + 1)| ≤ r ^ (n + 1) / (1 - r) := by
  have hx : |-u| < 1 := by rw [abs_neg]; linarith
  have hr0 : 0 ≤ r := le_trans (abs_nonneg _) hu
  have h := Real.abs_log_sub_add_sum_range_le hx n
  rw [sub_neg_eq_add, abs_neg] at h
  rw [sub_neg_eq_add, add_comm]
  refine le_trans h ?_
  have h3 : 0 < 1 - r := by linarith
  calc |u| ^ (n + 1) / (1 - |u|) ≤ r ^ (n + 1) / (1 - |u|) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hu _) (by linarith)
    _ ≤ r ^ (n + 1) / (1 - r) := div_le_div_of_nonneg_left (pow_nonneg hr0 _) h3 (by linarith)

include hT in
theorem ok_log {f : ℝ → ℝ} {A : TM} (hf : TMok m lo hi f A) :
    TMok m lo hi (fun t => Real.log (f t)) (TM.log C A) := by
  dsimp only [TM.log]
  split
  · rename_i hpos
    split
    · rename_i U r Y hrel hY
      obtain ⟨p0, hp0, hne, hr1, hU, hu⟩ := ok_rel hT hf hrel
      have hp := pos_of_posQ hpos hp0
      have hS : TMok m lo hi (fun t => Real.log (1 + (f t - p0) / p0)) _ :=
        ok_addR (X := DI.pm (r ^ (C.N + 2) / (1 - r))) (ok_ser hT hU (Interval128.Dy.coefs Interval128.Dy.lnCoef 0 (C.N + 1 + 1)))
          fun t h1 h2 => by
            apply mem_pm; rw [lnCoef_sum]
            have := log_bound (hu t h1 h2) (by exact_mod_cast hr1) (C.N + 1)
            push_cast; exact this
      refine (ok_add (ok_const (mem_log? hp0 hY)) hS).congr fun t h1 h2 => ?_
      have h1u : 0 < 1 + (f t - p0) / p0 := by
        have := hu t h1 h2
        have : (r : ℝ) < 1 := by exact_mod_cast hr1
        linarith [neg_abs_le ((f t - p0) / p0)]
      rw [← Real.log_mul hne h1u.ne']; congr 1; field_simp; ring
    · exact ok_whole _
  · exact ok_whole _

set_option linter.concreteInstances false
variable [ExtTbl] [ExtSem]

include hT in
theorem ok_tmE {M : DI} (hM : mem m M) :
    ∀ e : IExpr, TMok m lo hi (fun t => e.denote [t]) (Interval128.Dy.tmE C M e)
  | .var i => by
    unfold Interval128.Dy.tmE
    split
    · rename_i h; subst h; exact (ok_var hM).congr fun t _ _ => by simp [IExpr.denote]
    · exact ok_whole _
  | .rat q => (ok_const (I128Q.mem_ofRat q)).congr fun t _ _ => by simp [IExpr.denote]
  | .pi => (ok_const I128Q.mem_pi).congr fun t _ _ => by simp [IExpr.denote]
  | .add a b => (ok_add (ok_tmE hM a) (ok_tmE hM b)).congr fun t _ _ => by simp [IExpr.denote]
  | .sub a b => (ok_sub (ok_tmE hM a) (ok_tmE hM b)).congr fun t _ _ => by simp [IExpr.denote]
  | .mul a b => (ok_mul hT (ok_tmE hM a) (ok_tmE hM b)).congr fun t _ _ => by
      simp [IExpr.denote]
  | .div a b => (ok_mul hT (ok_tmE hM a) (ok_inv hT (ok_tmE hM b))).congr fun t _ _ => by
      simp [IExpr.denote, div_eq_mul_inv]
  | .neg a => (ok_neg (ok_tmE hM a)).congr fun t _ _ => by simp [IExpr.denote]
  | .inv a => (ok_inv hT (ok_tmE hM a)).congr fun t _ _ => by simp [IExpr.denote]
  | .pow a n => (ok_pow hT (ok_tmE hM a) n).congr fun t _ _ => by simp [IExpr.denote]
  | .exp a => (ok_exp hT (ok_tmE hM a)).congr fun t _ _ => by simp [IExpr.denote]
  | .log a => (ok_log hT (ok_tmE hM a)).congr fun t _ _ => by simp [IExpr.denote]
  | .sin a => (ok_sinCos hT false (ok_tmE hM a)).congr fun t _ _ => by simp [IExpr.denote, scR]
  | .cos a => (ok_sinCos hT true (ok_tmE hM a)).congr fun t _ _ => by simp [IExpr.denote, scR]
  | .sqrt _ | .abs _ | .atan _ | .atan2 _ _ | .sinh _ | .cosh _ | .tanh _ | .log2 _ | .log10 _
  | .tan _ | .asin _ | .acos _ | .ext _ _ _ => by unfold Interval128.Dy.tmE; exact ok_whole _

/-! ### Integration -/

omit [ExtTbl] [ExtSem] in
theorem mem_intP (qa qb : ℚ) : ∀ {p : List ℝ} {P : List DI} (k : ℕ), List.Forall₂ mem p P →
    mem (∫ x in (qa : ℝ)..qb, x ^ k * pv p x) (Interval128.Dy.intP qa qb k P)
  | [], [], k, .nil => by simpa [pv, Interval128.Dy.intP] using mem_zeroD
  | c :: p, _ :: _, k, .cons hc hp => by
    simp only [Interval128.Dy.intP]
    have e : (fun x : ℝ => x ^ k * pv (c :: p) x) = fun x => c * x ^ k + x ^ (k + 1) * pv p x := by
      funext x; simp only [pv]; ring
    have h1 : IntervalIntegrable (fun x : ℝ => c * x ^ k) MeasureTheory.volume (qa : ℝ) qb :=
      (continuous_const.mul (continuous_pow k)).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun x : ℝ => x ^ (k + 1) * pv p x) MeasureTheory.volume (qa : ℝ) qb :=
      ((continuous_pow (k + 1)).mul (continuous_pv p)).intervalIntegrable _ _
    rw [e, intervalIntegral.integral_add h1 h2,
      intervalIntegral.integral_const_mul, integral_pow]
    refine I128Q.mem_add (I128Q.mem_mul hc (I128Q.mem_ofRat' _ (by push_cast; ring))) (mem_intP qa qb (k + 1) hp)

omit [ExtTbl] [ExtSem] in
theorem rem_int {r : ℝ → ℝ} {R : DI} {a b : ℝ} (hab : a ≤ b)
    (hi : IntervalIntegrable r MeasureTheory.volume a b) (h : ∀ t, a ≤ t → t ≤ b → mem (r t) R) :
    ∃ c, mem c R ∧ ∫ t in a..b, r t = c * (b - a) := by
  rcases hab.eq_or_lt with hab | hab
  · subst hab; exact ⟨r a, h a le_rfl le_rfl, by simp⟩
  · have hw : 0 < b - a := by linarith
    refine ⟨(∫ t in a..b, r t) / (b - a), ⟨fun l hl => ?_, fun u hu => ?_⟩, by field_simp⟩
    · rw [le_div_iff₀ hw]
      have := intervalIntegral.integral_mono_on hab.le intervalIntegrable_const hi
        (fun t ht => (h t ht.1 ht.2).1 l hl)
      simpa [intervalIntegral.integral_const, mul_comm] using this
    · rw [div_le_iff₀ hw]
      have := intervalIntegral.integral_mono_on hab.le hi intervalIntegrable_const
        (fun t ht => (h t ht.1 ht.2).2 u hu)
      simpa [intervalIntegral.integral_const, mul_comm] using this

theorem cell_mem (N : ℕ) (e : IExpr) {lo hi : ℚ} (hle : lo ≤ hi)
    (hd : Interval128.Dy.domOKQ (Interval128.Dy.boxes [(lo, hi)]) e = true) :
    IntervalIntegrable (fun t => e.denote [t]) MeasureTheory.volume (lo : ℝ) hi ∧
      mem (∫ t in (lo : ℝ)..hi, e.denote [t]) (Interval128.Dy.cellQ N e lo hi) := by
  have hle' : (lo : ℝ) ≤ hi := by exact_mod_cast hle
  have hf : IntervalIntegrable (fun t => e.denote [t]) MeasureTheory.volume (lo : ℝ) hi :=
    (continuousOn_oneQ hd).intervalIntegrable_of_Icc hle'
  refine ⟨hf, ?_⟩
  unfold Interval128.Dy.cellQ
  dsimp only
  set qm : ℚ := (lo + hi) / 2 with hqm
  have hT : ∀ t : ℝ, (lo : ℝ) ≤ t → t ≤ hi → mem (t - (qm : ℝ)) (DI.ofRatI (lo - qm) (hi - qm)) ∧
      mem ((t - (qm : ℝ)) ^ N) (DI.pow (DI.ofRatI (lo - qm) (hi - qm)) N) := fun t h1 h2 =>
    have h := mem_ofRatI (x := t - (qm : ℝ)) (by push_cast; linarith) (by push_cast; linarith)
    ⟨h, I128Q.mem_pow h N⟩
  obtain ⟨p, hp, hr⟩ := ok_tmE (C := ⟨N, _, _⟩) hT (I128Q.mem_ofRat qm) e
  have hpc : Continuous fun t : ℝ => pv p (t - qm) := (continuous_pv p).comp (continuous_sub_right _)
  have hpi := hpc.intervalIntegrable (μ := MeasureTheory.volume) (lo : ℝ) hi
  obtain ⟨c, hc, hci⟩ := rem_int hle' (hf.sub hpi) hr
  have hsplit : (∫ t in (lo : ℝ)..hi, e.denote [t]) =
      (∫ t in (lo : ℝ)..hi, pv p (t - qm)) + ∫ t in (lo : ℝ)..hi, (e.denote [t] - pv p (t - qm)) := by
    rw [intervalIntegral.integral_sub hf hpi]; ring
  rw [hsplit, hci, intervalIntegral.integral_comp_sub_right (fun x => pv p x)]
  have hP := mem_intP (lo - qm) (hi - qm) 0 hp
  simp only [pow_zero, one_mul] at hP
  push_cast at hP
  refine I128Q.mem_add hP (I128Q.mem_mul hc (I128Q.mem_ofRat' _ (by push_cast; ring)))

theorem chain_mem (N : ℕ) (e : IExpr) : ∀ (ds : List ℚ) (lo : ℚ), Interval128.Dy.chainQ e lo ds = true →
    IntervalIntegrable (fun t => e.denote [t]) MeasureTheory.volume (lo : ℝ) (ds.getLastD lo) ∧
      mem (∫ t in (lo : ℝ)..(ds.getLastD lo : ℚ), e.denote [t]) (Interval128.Dy.quadQ N e lo ds)
  | [], lo, _ => by
    simp only [List.getLastD_nil, intervalIntegral.integral_same, Interval128.Dy.quadQ]
    exact ⟨IntervalIntegrable.refl, mem_zeroD⟩
  | hi :: rest, lo, h => by
    simp only [Interval128.Dy.chainQ, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hle, hd⟩, hrest⟩ := h
    have c := cell_mem N e hle hd
    have r := chain_mem N e rest hi hrest
    simp only [List.getLastD_cons, Interval128.Dy.quadQ]
    refine ⟨c.1.trans r.1, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals c.1 r.1]
    exact I128Q.mem_add c.2 r.2

/-- **Rigorous integral bounds** from a Taylor-model quadrature certificate at precision 128. -/
theorem integral_bounds_of_quadBoundQ {N : ℕ} {e : IExpr} {qa qb : ℚ} {ds : List ℚ} {ql qh : ℚ}
    (h : Interval128.Dy.quadBoundQ N e qa qb ds ql qh = true) :
    (ql : ℝ) ≤ (∫ x in (qa : ℝ)..qb, e.denote [x]) ∧ (∫ x in (qa : ℝ)..qb, e.denote [x]) ≤ qh := by
  unfold Interval128.Dy.quadBoundQ Interval128.Dy.bndsQ at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hl, hc⟩, h1, h2⟩ := h
  have hm := (chain_mem N e ds qa hc).2
  rw [hl] at hm
  exact ⟨I128Q.gGe_sound ql _ h1 _ hm, I128Q.gLe_sound qh _ h2 _ hm⟩

end RealFP.TMQ
