import ManyBoxFast

/-! C batch checker for manybox certificates.

`checkHex fe upper c d hex env` is, by definition, realfp-checkable `checkC3` on the decoded
certificate (`ManyBox.checkHex_eq`). Natively it is `@[implemented_by checkHexImpl]`: the
expression is compiled once to a flat tape and the whole tree walk (decode + per-leaf interval
evaluation + goal test) runs in C (`c/mbtape.c`, extern `mb_check_tape`), calling realfp's own
directed-rounding kernels `iv64_dir_*`. Same attach pattern as realfp's Bernstein checker
(`checkGeB` / `checkGeBImpl` / `iv64_bern_check`). Expressions with other nodes (div, sqrt,
transcendental), or arguments outside the C path's range, fall back to `checkC3`.

Trust: under `native_decide`, `mb_check_tape` is trusted to compute the spec. -/

open Interval64 Interval64.KF

namespace ManyBox

/-- Tape opcodes: 0 var, 1 const, 2 add, 3 sub, 4 mul, 5 neg, 6 pow. -/
abbrev TapeSt := Array UInt32 × Array Float

def emit (op a b : Nat) : StateT TapeSt Option Nat := do
  let (code, ks) ← get
  if a < 2 ^ 32 ∧ b < 2 ^ 32 then
    set (code.push op.toUInt32 |>.push a.toUInt32 |>.push b.toUInt32, ks)
    return code.size / 3
  else failure

def tapeAux : FExpr → StateT TapeSt Option Nat
  | .var i => emit 0 i 0
  | .const I => do
      let (code, ks) ← get
      set (code, ks.push I.lo |>.push I.hi)
      emit 1 (ks.size / 2) 0
  | .add a b => do let x ← tapeAux a; let y ← tapeAux b; emit 2 x y
  | .sub a b => do let x ← tapeAux a; let y ← tapeAux b; emit 3 x y
  | .mul a b => do let x ← tapeAux a; let y ← tapeAux b; emit 4 x y
  | .neg a => do let x ← tapeAux a; emit 5 x 0
  | .pow a n => do let x ← tapeAux a; emit 6 x n
  | _ => failure

def u32le (b : ByteArray) (x : UInt32) : ByteArray :=
  b.push x.toUInt8 |>.push (x >>> 8).toUInt8 |>.push (x >>> 16).toUInt8 |>.push (x >>> 24).toUInt8

/-- Flat tape (12 bytes per instruction) and constant pool, or `none` if unsupported. -/
def toTape (fe : FExpr) : Option (ByteArray × FloatArray) :=
  match (tapeAux fe).run (#[], #[]) with
  | some (_, (code, ks)) =>
      if code.size ≤ 3 * 4096 then
        some (code.foldl u32le ByteArray.empty, ⟨ks⟩)
      else none
  | none => none

def boxFA (env : List Interval64) : FloatArray :=
  ⟨(env.flatMap fun X => [X.lo, X.hi]).toArray⟩

/-- The C runtime (`c/mbtape.c`). -/
@[extern "mb_check_tape"]
opaque checkTapeExt (code : @& ByteArray) (ks : @& FloatArray) (upper : UInt8) (c : UInt64)
  (d : UInt32) (hex : @& String) (box : @& FloatArray) : Bool

def checkHexSpec [ExtTbl] (fe : FExpr) (upper : Bool) (c d : Nat) (hex : String)
    (env : List Interval64) : Bool :=
  checkC3 fe (if upper then gLe c else gGe c) (decodeCertC d hex) env

def checkHexImpl [ExtTbl] (fe : FExpr) (upper : Bool) (c d : Nat) (hex : String)
    (env : List Interval64) : Bool :=
  match toTape fe with
  | some (code, ks) =>
      if env.length == d && 0 < d && d ≤ 16 && c < 2 ^ 64 then
        checkTapeExt code ks (if upper then 1 else 0) c.toUInt64 d.toUInt32 hex (boxFA env)
      else checkHexSpec fe upper c d hex env
  | none => checkHexSpec fe upper c d hex env

/-- Certificate check, `upper`: `f ≤ c` (`gLe`), else `c ≤ f` (`gGe`). -/
@[implemented_by checkHexImpl]
def checkHex [ExtTbl] (fe : FExpr) (upper : Bool) (c d : Nat) (hex : String)
    (env : List Interval64) : Bool :=
  checkHexSpec fe upper c d hex env

theorem checkHex_le [ExtTbl] (fe : FExpr) (c d : Nat) (hex : String) (env : List Interval64) :
    checkHex fe true c d hex env = checkC3 fe (gLe c) (decodeCertC d hex) env := rfl

theorem checkHex_ge [ExtTbl] (fe : FExpr) (c d : Nat) (hex : String) (env : List Interval64) :
    checkHex fe false c d hex env = checkC3 fe (gGe c) (decodeCertC d hex) env := rfl

end ManyBox
