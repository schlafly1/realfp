import Interval64

/-! Compiled (precompiled) part of the manybox check. Mathlib-free.

* `decodeCertC d hex`: the preorder bit string of a GPU bisection tree (hex) → realfp `Cert`.
* `evalC`: realfp's hardware interval evaluator `evalI` (the `@[implemented_by]` C runtime) on
  bit-pattern boxes — the same definition as `RealFP.IntervalTactic.evalF`.
* `checkC`: walks a `Cert` like realfp's `checkK`, evaluating leaves with `evalC`.

Nothing here is trusted on its own: `ManyBox.checkC_sound` (in `../ManyBoxCert.lean`) proves
`checkC … = true → checkK … = true`. The point of this module is speed: built with
`precompileModules := true`, `native_decide` calls these functions as native code. -/

open Interval64 Interval64.KF

namespace ManyBox

@[inline] def hexValC (b : UInt8) : Nat :=
  if b ≥ 48 && b ≤ 57 then (b - 48).toNat
  else if b ≥ 97 && b ≤ 102 then (b - 87).toNat else 0

@[inline] def bitAtC (s : ByteArray) (i : Nat) : Bool :=
  (hexValC (s.get! (i / 4))).testBit (3 - i % 4)

/-- Midpoint `-1 + (2c+1) 2^-s` as binary64 bits (exact for `s ≤ 52`). -/
def midBitsC (c s : Nat) : Nat :=
  ((-1 : Float) + (2 * c + 1).toFloat * Float.scaleB 1 (-(s : Int))).toBits.toNat

partial def decC (d : Nat) (s : ByteArray) (l : Nat) (cs : Array Nat) (pos : Nat) : Cert × Nat :=
  if !bitAtC s pos then (.leaf, pos + 1)
  else
    let i := l % d
    let sp := (l + d - 1 - i) / d
    let c := cs[i]!
    let (L, p1) := decC d s (l + 1) (cs.set! i (2 * c)) (pos + 1)
    let (R, p2) := decC d s (l + 1) (cs.set! i (2 * c + 1)) p1
    (.split i (midBitsC c sp) L R, p2)

/-- Certificate from the hex preorder string of a `d`-dimensional manybox run on `[-1,1]^d`. -/
def decodeCertC (d : Nat) (hex : String) : Cert :=
  (decC d hex.toUTF8 0 (Array.replicate d 0) 0).1

def toFlC (n : Nat) : Float := Float.ofBits (UInt64.ofNat n)

/-- `evalK` computed by the C runtime (`evalI`); same body as `RealFP.IntervalTactic.evalF`. -/
def evalC [ExtTbl] (env : List KI) (e : IExpr) : KI :=
  let r := evalI (env.map fun X => ⟨toFlC X.lo, toFlC X.hi⟩) e
  ⟨r.lo.toBits.toNat, r.hi.toBits.toNat⟩

/-- `checkK` with leaves evaluated by `evalC`. -/
def checkC [ExtTbl] (e : IExpr) (g : KI → Bool) : Cert → List KI → Bool
  | .leaf, env => g (evalC env e)
  | .split i m l r, env =>
    !isNaN m && Nat.blt m (2 ^ 64) &&
      checkC e g l (env.set i ⟨(env.getD i zeroK).lo, m⟩) &&
      checkC e g r (env.set i ⟨m, (env.getD i zeroK).hi⟩)

/-! ### Constants evaluated once

`evalI` rounds every rational constant (`ofRat q`, exact rational arithmetic) at every
evaluation, which dominates a polynomial with many coefficients. `compile` replaces each
`.rat q` by its interval `ofRat q` once; `evalFE_compile` proves the result is unchanged. -/

inductive FExpr where
  | var (i : Nat)
  | const (I : Interval64)
  | add (a b : FExpr)
  | sub (a b : FExpr)
  | mul (a b : FExpr)
  | div (a b : FExpr)
  | neg (a : FExpr)
  | pow (a : FExpr) (n : Nat)
  | sqrt (a : FExpr)
  /-- Anything else is evaluated by `evalI` itself. -/
  | other (e : IExpr)
  deriving Inhabited

def compile : IExpr → FExpr
  | .var i => .var i
  | .rat q => .const (ofRat q)
  | .add a b => .add (compile a) (compile b)
  | .sub a b => .sub (compile a) (compile b)
  | .mul a b => .mul (compile a) (compile b)
  | .div a b => .div (compile a) (compile b)
  | .neg a => .neg (compile a)
  | .pow a n => .pow (compile a) n
  | .sqrt a => .sqrt (compile a)
  | e => .other e

def evalFE [ExtTbl] (env : List Interval64) : FExpr → Interval64
  | .var i => env.getD i zeroI
  | .const I => I
  | .add a b => evalFE env a + evalFE env b
  | .sub a b => evalFE env a - evalFE env b
  | .mul a b => evalFE env a * evalFE env b
  | .div a b => evalFE env a * inv (evalFE env b)
  | .neg a => -evalFE env a
  | .pow a n => pown (evalFE env a) n
  | .sqrt a => sqrtI (evalFE env a)
  | .other e => evalI env e

theorem evalFE_compile [ExtTbl] (env : List Interval64) (e : IExpr) :
    evalFE env (compile e) = evalI env e := by
  induction e <;> simp_all [compile, evalFE, evalI]

def evalC2 [ExtTbl] (env : List KI) (fe : FExpr) : KI :=
  let r := evalFE (env.map fun X => ⟨toFlC X.lo, toFlC X.hi⟩) fe
  ⟨r.lo.toBits.toNat, r.hi.toBits.toNat⟩

theorem evalC2_compile [ExtTbl] (env : List KI) (e : IExpr) : evalC2 env (compile e) = evalC env e := by
  simp only [evalC2, evalC, evalFE_compile]

/-- `checkC` on a compiled expression. -/
def checkC2 [ExtTbl] (fe : FExpr) (g : KI → Bool) : Cert → List KI → Bool
  | .leaf, env => g (evalC2 env fe)
  | .split i m l r, env =>
    !isNaN m && Nat.blt m (2 ^ 64) &&
      checkC2 fe g l (env.set i ⟨(env.getD i zeroK).lo, m⟩) &&
      checkC2 fe g r (env.set i ⟨m, (env.getD i zeroK).hi⟩)

theorem checkC2_compile [ExtTbl] (e : IExpr) (g : KI → Bool) :
    ∀ (c : Cert) (env : List KI), checkC2 (compile e) g c env = checkC e g c env := by
  intro c
  induction c with
  | leaf => intro env; simp only [checkC2, checkC, evalC2_compile]
  | split i m l r ihl ihr => intro env; simp only [checkC2, checkC, ihl, ihr]

/-! ### Float boxes in the tree walk

`checkC3` keeps the current box as `Interval64` (Float endpoints) instead of bit patterns, so a
leaf costs one `evalFE` and no `Nat` ↔ `Float` conversion of the box. `checkC3_map` proves it
equals `checkC2` on the converted box list. -/

@[inline] def toIC (X : KI) : Interval64 := ⟨toFlC X.lo, toFlC X.hi⟩
@[inline] def bitsOf (r : Interval64) : KI := ⟨r.lo.toBits.toNat, r.hi.toBits.toNat⟩

def checkC3 [ExtTbl] (fe : FExpr) (g : KI → Bool) : Cert → List Interval64 → Bool
  | .leaf, env => g (bitsOf (evalFE env fe))
  | .split i m l r, env =>
    !isNaN m && Nat.blt m (2 ^ 64) &&
      checkC3 fe g l (env.set i ⟨(env.getD i (toIC zeroK)).lo, toFlC m⟩) &&
      checkC3 fe g r (env.set i ⟨toFlC m, (env.getD i (toIC zeroK)).hi⟩)

theorem getD_map_toIC (env : List KI) (i : Nat) :
    (env.map toIC).getD i (toIC zeroK) = toIC (env.getD i zeroK) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map]

theorem checkC3_map [ExtTbl] (fe : FExpr) (g : KI → Bool) :
    ∀ (c : Cert) (env : List KI), checkC3 fe g c (env.map toIC) = checkC2 fe g c env := by
  intro c
  induction c with
  | leaf => intro env; rfl
  | split i m l r ihl ihr =>
    intro env
    simp only [checkC3, checkC2, getD_map_toIC]
    rw [← ihl, ← ihr, List.map_set, List.map_set]
    rfl

end ManyBox
