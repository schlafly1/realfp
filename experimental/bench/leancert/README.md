# LeanCert comparison problems via `realfp`

The goal statements of the head-to-head comparison with
[LeanCert](https://github.com/alerad/leancert) (`44b323a`, Lean 4.35), each closed by the single
front-door tactic `realfp` in kernel mode. Run `./run.sh` (needs a built `RealFPMathlib`).
`results-2026-11-23.txt` is one run on a shared 8-CPU Linux box (median of 3, wall time
including ≈3.4 s of imports; single outliers are box contention).

| Goal | realfp (s) | LeanCert `leancert (trust := kernel)` (s) |
|---|---|---|
| x01 `∃! x, x ∈ Icc 1 2 ∧ x² − 2 = 0` | 3.84 | 5.03 |
| p07 `∀ x ∈ [0,1], sin x ≤ x + 1/1000` | 4.23 | router fails; 63 s with subdivision |
| p10 `∀ x y ∈ [0,1], sin x cos y ≤ 1.01` | 4.82 | 24.8 |
| p14 `0.74 ≤ ∫₀¹ e^{−x²}` | 4.67 | 89.5 |
| p15 `0.7468 ≤ ∫₀¹ e^{−x²}` | 5.72 | fails (native: 53 s) |
| x03 2×2 system, `∃!` (Krawczyk) | 4.46 | — |

realfp proves 20 of the 21 shared bound/integral goals plus x01, all with standard axioms only;
p17 (`∫₀¹ arctan ≤ 0.43882`, margin 4.6·10⁻⁶) fails for both tools.
