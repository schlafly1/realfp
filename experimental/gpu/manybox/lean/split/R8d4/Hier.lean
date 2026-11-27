import ManyBoxCert
import ManyBoxProbs
import split.TopC
import split.R8d4.H00
import split.R8d4.H01
import split.R8d4.H02
import split.R8d4.H03
import split.R8d4.H04
import split.R8d4.H05
import split.R8d4.H06
import split.R8d4.H07
import split.R8d4.H08
import split.R8d4.H09
import split.R8d4.H10
import split.R8d4.H11
import split.R8d4.H12
import split.R8d4.H13
import split.R8d4.H14
import split.R8d4.H15
open Interval64.KF ManyBox
set_option profiler true
set_option profiler.threshold 200
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! Split certificate `R8d4`: # manybox2 split prob R8 delta 4 prec 64 dim 8 K 8
    256 sub-checks in 16 files, glued in two levels (gen_hier.py). -/

namespace ManyBox.Split.R8d4

noncomputable def top2 : TopC :=
.split 0 0
 (.split 1 0
 (.split 2 0
 (.split 3 0
 (.leaf (H00.t.toCert 8))
 (.leaf (H01.t.toCert 8)))
 (.split 3 0
 (.leaf (H02.t.toCert 8))
 (.leaf (H03.t.toCert 8))))
 (.split 2 0
 (.split 3 0
 (.leaf (H04.t.toCert 8))
 (.leaf (H05.t.toCert 8)))
 (.split 3 0
 (.leaf (H06.t.toCert 8))
 (.leaf (H07.t.toCert 8)))))
 (.split 1 0
 (.split 2 0
 (.split 3 0
 (.leaf (H08.t.toCert 8))
 (.leaf (H09.t.toCert 8)))
 (.split 3 0
 (.leaf (H10.t.toCert 8))
 (.leaf (H11.t.toCert 8))))
 (.split 2 0
 (.split 3 0
 (.leaf (H12.t.toCert 8))
 (.leaf (H13.t.toCert 8)))
 (.split 3 0
 (.leaf (H14.t.toCert 8))
 (.leaf (H15.t.toCert 8)))))

def env0 : List KI := [⟨13830554455654793216, 4607182418800017408⟩, ⟨13830554455654793216, 4607182418800017408⟩, ⟨13830554455654793216, 4607182418800017408⟩, ⟨13830554455654793216, 4607182418800017408⟩, ⟨13830554455654793216, 4607182418800017408⟩, ⟨13830554455654793216, 4607182418800017408⟩, ⟨13830554455654793216, 4607182418800017408⟩, ⟨13830554455654793216, 4607182418800017408⟩]

theorem env0_eq : boxes (V2.cube 8) = env0 := by decide +kernel

theorem midsOK2 : top2.midsOK = true := by decide +kernel

theorem leaves_eq : top2.leaves env0 = [(H00.t.toCert 8, H00.env), (H01.t.toCert 8, H01.env), (H02.t.toCert 8, H02.env), (H03.t.toCert 8, H03.env), (H04.t.toCert 8, H04.env), (H05.t.toCert 8, H05.env), (H06.t.toCert 8, H06.env), (H07.t.toCert 8, H07.env), (H08.t.toCert 8, H08.env), (H09.t.toCert 8, H09.env), (H10.t.toCert 8, H10.env), (H11.t.toCert 8, H11.env), (H12.t.toCert 8, H12.env), (H13.t.toCert 8, H13.env), (H14.t.toCert 8, H14.env), (H15.t.toCert 8, H15.env)] := rfl

theorem all : checkC2 (compile V2.eR8) (if false then gLe (KI.ofRat (-12)).hi else gGe (KI.ofRat (-12)).hi) top2.toCert env0 = true :=
  TopC.sound _ _ top2 env0 midsOK2 (by rw [leaves_eq]; exact ⟨H00.sub, ⟨H01.sub, ⟨H02.sub, ⟨H03.sub, ⟨H04.sub, ⟨H05.sub, ⟨H06.sub, ⟨H07.sub, ⟨H08.sub, ⟨H09.sub, ⟨H10.sub, ⟨H11.sub, ⟨H12.sub, ⟨H13.sub, ⟨H14.sub, ⟨H15.sub, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

/-- The claim on the whole cube, from 256 sub-checks in 16 files. -/
theorem bound2 (xs : List ℝ) (hxs : RealFP.InBoxes xs (V2.cube 8)) : ((-12 : ℚ) : ℝ) ≤ V2.eR8.denote xs := by
  have h := all
  rw [← env0_eq] at h
  simp only [Bool.false_eq_true, ↓reduceIte, checkC2_compile] at h
  exact proveC_ge V2.eR8 (V2.cube 8) (-12) _ h xs hxs

end ManyBox.Split.R8d4

#print axioms ManyBox.Split.R8d4.bound2
