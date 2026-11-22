/-
Expression tapes: `IExpr` compiled to straight-line code for the C evaluator
(`c/iv64_quad.h`). Untrusted runtime plumbing only: nothing is proved about tapes; the
C routines that use them are attached with `@[implemented_by]` to Lean specifications
written with `KF.evalI`, and the differential tests check that the results agree bit for bit.

Instruction `i` is three little-endian `u32` words `op, a, b` writing register `i`; equal
instructions are shared (common subexpressions are evaluated once). Constants (`rat`, `pi`)
are precomputed `Interval64` values. Elementary functions are called back as Lean closures
(`unaryFns`, `atan2I`), so they are the same functions as in `evalI`.
-/
import Std.Data.HashMap
import Interval64.Kernel.Reflect

namespace Interval64.KF.Tape

open Std

/-- The unary elementary functions of `evalI`, in opcode order. -/
def unaryFns : Array (Interval64 → Interval64) :=
  #[Interval64.exp, logI, Interval64.sin, Interval64.cos, Interval64.atan, Interval64.sinh,
    Interval64.cosh, Interval64.tanh, logBI false, logBI true, Interval64.tan, Interval64.asin,
    Interval64.acos]

def atan2Fn : Interval64 → Interval64 → Interval64 := atan2I

structure St where
  code : ByteArray := ByteArray.empty
  consts : FloatArray := FloatArray.empty
  n : UInt32 := 0
  nk : UInt32 := 0
  memo : HashMap (UInt32 × UInt32 × UInt32) UInt32 := {}
  kmemo : HashMap (UInt64 × UInt64) UInt32 := {}
  ok : Bool := true

def push32 (b : ByteArray) (x : UInt32) : ByteArray :=
  ((b.push x.toUInt8).push (x >>> 8).toUInt8 |>.push (x >>> 16).toUInt8).push (x >>> 24).toUInt8

abbrev M := StateM St

def emit (op a b : UInt32) : M UInt32 := do
  let s ← get
  match s.memo.get? (op, a, b) with
  | some r => return r
  | none =>
    let r := s.n
    if r == 0xFFFFFFFF then set { s with ok := false }; return 0
    set { s with code := push32 (push32 (push32 s.code op) a) b, n := r + 1,
                 memo := s.memo.insert (op, a, b) r }
    return r

def emitConst (X : Interval64) : M UInt32 := do
  let s ← get
  let key := (X.lo.toBits, X.hi.toBits)
  let k ← match s.kmemo.get? key with
    | some k => pure k
    | none => do
      set { s with consts := (s.consts.push X.lo).push X.hi, nk := s.nk + 1,
                   kmemo := s.kmemo.insert key s.nk }
      pure s.nk
  emit 1 k 0

def small (n : Nat) : M UInt32 := do
  if n < 2 ^ 32 then return n.toUInt32
  modify fun s => { s with ok := false }; return 0

partial def comp : IExpr → M UInt32
  | .var i => do emit 0 (← small i) 0
  | .rat q => emitConst (ofRat q)
  | .pi => emitConst Interval64.pi
  | .add a b => do let x ← comp a; let y ← comp b; emit 2 x y
  | .sub a b => do let x ← comp a; let y ← comp b; emit 3 x y
  | .mul a b => do let x ← comp a; let y ← comp b; emit 4 x y
  | .div a b => do let x ← comp a; let y ← comp b; emit 5 x y
  | .neg a => do emit 6 (← comp a) 0
  | .inv a => do emit 7 (← comp a) 0
  | .sqrt a => do emit 8 (← comp a) 0
  | .abs a => do emit 9 (← comp a) 0
  | .pow a n => do let x ← comp a; emit 10 x (← small n)
  | .exp a => do emit 11 (← comp a) 0
  | .log a => do emit 11 (← comp a) 1
  | .sin a => do emit 11 (← comp a) 2
  | .cos a => do emit 11 (← comp a) 3
  | .atan a => do emit 11 (← comp a) 4
  | .sinh a => do emit 11 (← comp a) 5
  | .cosh a => do emit 11 (← comp a) 6
  | .tanh a => do emit 11 (← comp a) 7
  | .log2 a => do emit 11 (← comp a) 8
  | .log10 a => do emit 11 (← comp a) 9
  | .tan a => do emit 11 (← comp a) 10
  | .asin a => do emit 11 (← comp a) 11
  | .acos a => do emit 11 (← comp a) 12
  | .atan2 y x => do let a ← comp y; let b ← comp x; emit 12 a b

/-- A compiled tape with the registers of the given roots. -/
structure Tape where
  code : ByteArray
  consts : FloatArray
  roots : Array UInt32
  deriving Inhabited

def Tape.rootBytes (t : Tape) : ByteArray := t.roots.foldl push32 ByteArray.empty

/-- Compile several expressions into one tape (shared subexpressions); `none` if an index or
    exponent does not fit in `u32`. -/
def compile (es : List IExpr) : Option Tape :=
  let (roots, s) := (es.mapM comp).run {}
  if s.ok then some ⟨s.code, s.consts, roots.toArray⟩ else none

/-- Number of instructions. -/
def Tape.size (t : Tape) : Nat := t.code.size / 12

@[extern "iv64_tape_eval"]
opaque evalC (code : @& ByteArray) (consts : @& FloatArray) (fns : @& Array (Interval64 → Interval64))
  (atan2 : @& (Interval64 → Interval64 → Interval64)) (root : UInt32) (env : @& Array Interval64) :
  Interval64

/-- `evalI env e` by the C tape evaluator (untrusted; for tests and benchmarks). -/
def evalTape (env : List Interval64) (e : IExpr) : Interval64 :=
  match compile [e] with
  | some t => evalC t.code t.consts unaryFns atan2Fn t.roots[0]! env.toArray
  | none => evalI env e

end Interval64.KF.Tape
