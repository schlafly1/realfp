import Interval64
open Interval64 Interval64.Quad Interval64.KF
def g : IExpr := .exp (.neg (.mul (.var 0) (.var 0)))
#eval let r := integrateE0 g 0 1 1e-6 14; (r.lo, r.hi, r.hi - r.lo)
#eval let r := integrateE1 g 0 1 1e-12 10; (r.lo, r.hi, r.hi - r.lo)
#eval let r := integrateE1 g 0 1 1e-14 14; (r.lo, r.hi, r.hi - r.lo)
#eval let r := polyIntegral #[⟨1,1⟩, ⟨0,0⟩, ⟨3,3⟩] ⟨0,0⟩ ⟨2,2⟩; (r.lo, r.hi)  -- ∫0^2 1+3x^2 = 2 + 8 = 10
