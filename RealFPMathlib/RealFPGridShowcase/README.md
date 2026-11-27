# RealFPGridShowcase

These are big `interval_grid` proofs, built only by `grid/showcase.sh`; they are not part of
any default build. The timings and the background are in
[docs/GPU.md](../../docs/GPU.md#showcases-and-timings).

| file | theorem | how to build | measured on DGX Spark |
|---|---|---|---|
| `R8.lean` | `r8_ge`: `Σᵢ T₄(xᵢ)T₄(xᵢ₊₁) ≥ −9` on `[−1, 1]⁸`, 5.3·10⁹ leaves | `grid/showcase.sh r8 R8 16 8 gpu64` | 611 s total |
| `M6.lean` | `m6_ge`: Reznick's AM–GM form `≥ −1/4` on `[−1, 1]⁶`, 6.5·10⁹ leaves | `grid/showcase.sh m6 M6 16 8 gpu64` | 464 s total |
| `Nesbitt.lean` | `nesbitt_split`: the split workflow on a small problem | `grid/showcase.sh nesbitt Nesbitt 9 3` | 13.6 s (x86 box, CPU) |

* **Problem files:** `Export.lean` writes them (`#grid_export`) into `problems/`.
* **Generated files:** they go to `Gen/` (git-ignored, 2.7–3.1 GB for R8 and M6). They are
  untrusted, because Lean checks everything.
* **Axioms:** `#print axioms r8_ge` (and `m6_ge`) lists `propext`, `Classical.choice`,
  `Quot.sound` and 256 `…native_decide.ax_…` axioms, one per group module. No `sorry`.
