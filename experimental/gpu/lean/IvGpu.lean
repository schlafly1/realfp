/-! Calling the Interval64 CUDA kernels from Lean through the C FFI.

Standalone demo (not part of `lake build`); build with `gpu/lean/build.sh`.
The GPU results here are *not* kernel-checked: they are as trusted as the
CUDA toolchain, driver and GPU (like `native_decide`). -/

/-- Grid evaluation of benchmark function `fn` on `2^k × 2^k` boxes.
Returns `#[min lo, max hi, failing boxes, kernel ms]`. -/
@[extern "lean_ivgpu_grid"]
opaque gpuGrid (fn : UInt32) (k : UInt32) : IO FloatArray

/-- `boxes` holds `xlo, xhi, ylo, yhi` per box; result holds `lo, hi` per box. -/
@[extern "lean_ivgpu_list"]
opaque gpuList (fn : UInt32) (boxes : @& FloatArray) : IO FloatArray

def timeIt (reps : Nat) (act : IO α) : IO Float := do
  let t0 ← IO.monoNanosNow
  for _ in [0:reps] do discard act
  let t1 ← IO.monoNanosNow
  return (t1 - t0).toFloat / reps.toFloat / 1000.0   -- µs per call

def main : IO Unit := do
  for (fn, k, claim) in [((0 : UInt32), (11 : UInt32), "f0 = Motzkin >= -1/64 on [-2,2]^2"),
                         (1, 11, "f1 = (x+y)/sqrt(2(x^2+y^2+1)) <= 0.99 on [-4,4]^2")] do
    let r ← gpuGrid fn k
    let us ← timeIt 50 (gpuGrid fn k)
    IO.println s!"{claim}: 2^{2*k} boxes, min lo = {r[0]!}, max hi = {r[1]!}, failing boxes = {r[2]!}, \
      kernel {r[3]!} ms, Lean call {us} us"
  -- per-call overhead from Lean: one box, and 2^20 boxes
  let one := FloatArray.mk #[0.5, 0.75, -1.0, 1.0]
  let o ← gpuList 1 one
  IO.println s!"one box [0.5,0.75]x[-1,1] -> f1 in [{o[0]!}, {o[1]!}]"
  let us1 ← timeIt 2000 (gpuList 1 one)
  IO.println s!"gpuList, 1 box: {us1} us per Lean call"
  let mut big : FloatArray := FloatArray.emptyWithCapacity (4 * 1048576)
  for i in [0:1048576] do
    let x := (i % 1024).toFloat / 256.0 - 2.0
    let y := (i / 1024).toFloat / 256.0 - 2.0
    big := (((big.push x).push (x + 1.0/256.0)).push y).push (y + 1.0/256.0)
  let usb ← timeIt 20 (gpuList 1 big)
  IO.println s!"gpuList, 2^20 boxes: {usb} us per Lean call ({1048576.0 / usb} M boxes/s incl. copies)"
