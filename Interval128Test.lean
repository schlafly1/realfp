import Interval128Tests

def main : IO UInt32 := do
  let n ← Interval128Tests.run
  return (if n == 0 then 0 else 1)
