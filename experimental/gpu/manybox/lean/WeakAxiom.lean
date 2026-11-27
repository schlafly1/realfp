import ManyBoxCert
import ManyBoxProbs
open Interval64.KF ManyBox

/-! "Weaker than proof" demo (b): a GPU result as a *labeled assumption*.

EXPERIMENTAL FILE ONLY. The axiom below is NOT proved by Lean; it records a search result so
that everything depending on it shows the gap in `#print axioms`. Never use this pattern in the
core library.

* Claim: `R8(x) = Σᵢ T4(xᵢ) T4(xᵢ₊₁ mod 8) ≥ -9` on `[-1,1]⁸` (true minimum −8; margin δ = 1).
* Search: v2 GPU engine, fp64 directed rounding (CUDA `__dadd_rd` etc.), 1.07e10 boxes,
  5,343,745,536 leaves, 41 s on the GB10 (fp32: 18 s, same boxes).
* Certificate: `mb2 split R8 64 1 16 DIR` (233 s on the GB10, 65,536 sub-certificates,
  1.3 GB hex); combined hash `fnv 893675208e4e9f33` (FNV-1a fold of the per-job FNV-1a hashes,
  printed by `mb2 split`).
* To turn it into a theorem: `split/gen_split.py DIR R8d1 V2.eR8 false -9 N` and
  `split/run_split.sh R8d1 P T` — the same pipeline that proves R8 δ=4 and δ=2 in
  `split/R8d4`, `split/R8d2`; estimated ~45 min on 8 x86 cores at the measured C-checker rate
  (~2e6 R8 leaves/s), not run here (moving 1.3 GB to the checking machine was the bottleneck).
* Partial evidence in Lean: `WeakSample.lean` (64 random leaves, kernel-checked). -/

namespace ManyBox.Assumed

/-- UNPROVED GPU search result (see the module comment: certificate hash
`fnv 893675208e4e9f33`, reproduce with `v2/build/mb2 split R8 64 1 16 DIR`). -/
axiom gpu_R8_ge_neg9 : ∀ xs : List ℝ, RealFP.InBoxes xs (V2.cube 8) → ((-9 : ℚ) : ℝ) ≤ V2.eR8.denote xs

/-- A downstream use (8 explicit reals); its axioms list `gpu_R8_ge_neg9`. -/
theorem ring_ge (a b c d e f g h : ℝ) (ha : -1 ≤ a ∧ a ≤ 1) (hb : -1 ≤ b ∧ b ≤ 1) (hc : -1 ≤ c ∧ c ≤ 1) (hd : -1 ≤ d ∧ d ≤ 1) (he : -1 ≤ e ∧ e ≤ 1) (hf : -1 ≤ f ∧ f ≤ 1) (hg : -1 ≤ g ∧ g ≤ 1) (hh : -1 ≤ h ∧ h ≤ 1) :
    (-9 : ℝ) ≤ V2.eR8.denote [a, b, c, d, e, f, g, h] := by
  have := gpu_R8_ge_neg9 [a, b, c, d, e, f, g, h] (by simp only [V2.cube, List.replicate]; mb_inboxes)
  simpa using this

/-- …and a further consequence, e.g. a weaker bound. -/
theorem ring_ge' (a b c d e f g h : ℝ) (ha : -1 ≤ a ∧ a ≤ 1) (hb : -1 ≤ b ∧ b ≤ 1) (hc : -1 ≤ c ∧ c ≤ 1) (hd : -1 ≤ d ∧ d ≤ 1) (he : -1 ≤ e ∧ e ≤ 1) (hf : -1 ≤ f ∧ f ≤ 1) (hg : -1 ≤ g ∧ g ≤ 1) (hh : -1 ≤ h ∧ h ≤ 1) :
    (-10 : ℝ) ≤ V2.eR8.denote [a, b, c, d, e, f, g, h] := by
  linarith [ring_ge a b c d e f g h ha hb hc hd he hf hg hh]

end ManyBox.Assumed

#print axioms ManyBox.Assumed.ring_ge'
