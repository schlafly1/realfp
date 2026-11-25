# Polished examples

These files are short, self-contained proofs of famous inequalities
and constants. Each starts with a comment describing the mathematics, a
single `import RealFPMathlib`, and theorems closed by `realfp` or
`integral_bound` in the default kernel-checked mode (Lean's standard
axioms only: `propext`, `Classical.choice`, `Quot.sound`). Copy any one
into a Mathlib project that requires `realfp_mathlib`, or run it from a
checkout of this repository:

```bash
cd RealFPMathlib
lake lean RealFPMathlib/Examples/Constants.lean
```

| File | What it proves |
|------|----------------|
| [Constants.lean](../RealFPMathlib/RealFPMathlib/Examples/Constants.lean) | `π`, `e`, `√2` and the golden ratio `(1+√5)/2` to 30 decimals (`precision := 128`); Archimedes' bounds `223/71 < π < 22/7` |
| [ExpPi.lean](../RealFPMathlib/RealFPMathlib/Examples/ExpPi.lean) | `e^π > π^e`, written as `π > e log π` |
| [Gaussian.lean](../RealFPMathlib/RealFPMathlib/Examples/Gaussian.lean) | `∫₀¹ exp(-x²) dx` to four decimals, and to 18 significant digits at `precision := 128` |
| [Jordan.lean](../RealFPMathlib/RealFPMathlib/Examples/Jordan.lean) | `x − x³/6 ≤ sin x ≤ x` and Jordan's inequality `(2/π) x ≤ sin x` on `[0, 157/100] ⊂ [0, π/2]` |
| [LogIneq.lean](../RealFPMathlib/RealFPMathlib/Examples/LogIneq.lean) | `x/(1+x) ≤ log(1+x) ≤ x ≤ exp(x) − 1` on `[0, 10]` |
| [AMGM.lean](../RealFPMathlib/RealFPMathlib/Examples/AMGM.lean) | Equality at an interior point, with `realfp (touch := [p])`: AM–GM `√x ≤ (1+x)/2` on `[0, 10]`, `log x ≤ x − 1` on `[1/10, 10]`, `1 + x ≤ eˣ` on `[-2, 5]` |
| [Motzkin.lean](../RealFPMathlib/RealFPMathlib/Examples/Motzkin.lean) | The Motzkin polynomial `x⁴y² + x²y⁴ − 3x²y² + 1 ≥ 0` on `[-2, 2]²` (zeros at `(±1, ±1)`; nonnegative but not a sum of squares), via `realfp (touch := [(1, 1)])` on a quadrant |

The tactic needs numeral endpoints, which is why Jordan's interval is
written `157/100 = 1.57` rather than `π/2`. AMGM and Motzkin need the
`(touch := …)` option: their bound is attained at an interior point, where
every enclosing box dips below the bound. See "Touching points" in the
[reference](REFERENCE.md). Each file elaborates in well
under 30 seconds once the library is built (Jordan is the slowest, at
about 18 s). They are compiled by the weekly Examples workflow and, being
inexpensive, also by the push-CI axiom audit (`AxiomAuditCore`).

Further feature-oriented examples (roots, matrices, precision-128 test
cases, the compiled tutorial snippets, and so on) live in the same
[Examples/](../RealFPMathlib/RealFPMathlib/Examples/) directory and are
described in the [tutorial](TUTORIAL.md).
