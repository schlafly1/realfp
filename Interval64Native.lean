import Interval64
import Interval64.NativeDecide

open Interval64 Interval64.Directed Interval64.NativeDecide

def main : IO UInt32 := do
  IO.println "----- native_decide demo -----"
  IO.println s!"demoIv = {repr demoIv}"
  IO.println s!"(demoIv * demoIv + demoIv).hi = {demoHi}"
  IO.println s!"demoHi_le_bool (compiled decide) = {demoHi_le_bool}"

  -- Pass a runtime token so the impure C calls cannot be constant-folded.
  let tok0 ← IO.monoNanosNow
  let tok := UInt64.ofNat tok0
  let resetVal := debugReset tok
  let c0 := debugCount (tok + 1)
  -- A fresh interval computation (not the already-evaluated `demoHi`).
  let iv : Interval64 := ⟨0.25, 0.75⟩ * ⟨0.25, 0.75⟩ + ⟨0.25, 0.75⟩
  let c1 := debugCount (tok + 2)
  IO.println s!"debugReset returned {resetVal}"
  IO.println s!"C debug counter after reset: {c0}"
  IO.println s!"C debug counter after compiled interval ops: {c1}  (hi={iv.hi})"
  if c1 > c0 then
    IO.println "Runtime path: compiled Interval64 ops called the AVX-512 C kernels (counter increased)."
  else
    IO.println "Runtime path: C counter did not increase."

  -- Timing uses a start value derived from the clock so the loop cannot be
  -- constant-folded at compile time.
  let tBase ← IO.monoNanosNow
  let start := Float.ofNat (tBase % 3 + 1)
  let n := 2000000
  let rec loopC (k : Nat) (acc : Float) : Float :=
    match k with
    | 0 => acc
    | k'+1 => loopC k' (addDown acc start)
  let rec loopS (k : Nat) (acc : Float) : Float :=
    match k with
    | 0 => acc
    | k'+1 => loopS k' (addDownSpec acc start)
  let _ := loopC 100 start
  let _ := loopS 20 start
  let t0 ← IO.monoNanosNow
  let rC := loopC n start
  let t1 ← IO.monoNanosNow
  let nS := 20000
  let rS := loopS nS start
  let t2 ← IO.monoNanosNow
  let nsC := (t1 - t0).toFloat / Float.ofNat n
  let nsS := (t2 - t1).toFloat / Float.ofNat nS
  IO.println s!"addDown     (implemented_by, {n} ops): {nsC} ns/op  acc={rC}"
  IO.println s!"addDownSpec (Lean software, {nS} ops): {nsS} ns/op  acc={rS}"
  if decide (nsS > nsC * 5) then
    IO.println "Timing: addDown is substantially faster than addDownSpec, consistent with the C kernel."
  else
    IO.println "Timing: no large gap; the compiled addDown path may be the Lean spec."

  if demoHi_le_bool && decide (iv.hi ≤ 1.5) && c1 > c0 then
    IO.println "native_decide demo: OK"
    return 0
  else
    IO.println "native_decide demo: FAILED"
    return 1

-- Compile-time axiom report (also appears in `lake build` logs):
#print axioms demoHi_le
#print axioms Interval64.Theorems.add_one_halfUlp
#print axioms Interval64.Theorems.addU_nan_left
#print axioms Interval64.Theorems.awayFromZero_pos
#print axioms Interval64.Theorems.pack_notANumber
#print axioms Interval64.Theorems.roundMantissaDirected_exact
