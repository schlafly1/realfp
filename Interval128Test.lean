import Interval128Tests
import Interval128DyTests

def main : IO UInt32 := do
  let n ← Interval128Tests.run
  let m ← Interval128DyTests.run
  return (if n + m == 0 then 0 else 1)
