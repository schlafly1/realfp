# Known limitations

Current as of November 2026. These are known gaps, not bugs in soundness:
every proof that succeeds is checked by Lean, and the axiom audit runs in the default build.

## Extension registry (`Registry.lean`)
- Registered functions must be unary (`f a`), and their derivatives must be built from built-in functions.
- There is no C fast path for registered functions; they are evaluated through the Lean spec.
- `integral_bound` uses order ≤ 4 by default for registered functions.
- There is no 2D quadrature for registered functions.

## Specific functions
- **sinc:** the derivative formula (x cos x − sin x)/x² is undefined at 0, so boxes containing 0
  get plain bounds only (no derivative-based methods). An integral over a range containing 0,
  such as ∫₀¹ sinc, currently fails.
- **artanh:** boxes must lie strictly inside (−1, 1); boxes touching ±1 are rejected.
- **erf:** defined via its integral (Mathlib has no erf); enclosures are about 1e-9 wide.

## Kernel cost
- In kernel mode each `log` costs about 0.1 s and each `sin`/`cos` about 0.5 s, so tight bounds
  can hit heartbeat limits. Five tight examples (two sinc roots, a tight sinc minimum, two tight
  artanh bounds) use `trust := native`; looser versions of each are kernel-checked.
- Example files for the new functions take 37–104 s each to build.

## Precision 128 (`(precision := 128)`)
- **Functions.** `arctan`, `atan2`, `tan`, `arcsin`, `arccos`, registered functions, and
  `log` / `logb` on intervals not known to be positive are evaluated with Interval64 precision
  (about `1e-16` relative), and the failure message lists them.
- **`sin`/`cos` accuracy.** It degrades for large arguments: about `3e-31` relative near
  `x ≈ 10³`, because the double-angle steps amplify the error. An interval `sin`/`cos` is
  centre `±` radius, so wide intervals are coarse.
- **Certificates.** Derivative certificates are the one-variable-at-a-time `DCert`
  (bisection, monotonicity, centred form). The multivariate centred forms (`MCert`) and the
  Taylor and Bernstein certificates of precision 64 do not exist at 128. Registered functions
  are never differentiated at 128, and `≠` is plain bisection.
- **Kernel cost.**
  - Arithmetic: about 10–30 ms per box.
  - Elementary functions: about 0.1–0.7 s per point evaluation, with two per interval for
    `exp`/`log`/hyperbolic.
  - A tight bound at an interior maximum of `sin x + cos x` (`1e-16` margin: 30 splits and
    36 monotonicity steps) takes 36–55 s in the kernel and about 0.9 s with
    `(trust := native)`.
- **Krawczyk.** The preconditioner `Y` is a binary64 inverse, so Jacobians with condition
  number near `10¹⁶` fail. `∃!` needs contraction on the whole given box.
- **Optimisation.** Argmin/argmax localisation is one-variable only, and the box width is
  limited to about `10⁻¹⁶` by the quadratic value gap. `#realfp_min` / `#realfp_max` at 128 are
  untrusted reports.
- **Integrals (`integral_bound`).**
  - One variable only.
  - Supported: `+ - * / ^n`, rationals, `π`, `exp`, `sin`, `cos`, `log`. Other functions
    make the search fail.
  - `1/·` and `log` need the argument away from 0 on each cell.
  - At most 64 cells by default, and orders 8–30.
  - Kernel time is about 0.15 s per Taylor-model product, so it grows with cells × order.
    Integrands that need many cells are slow in the kernel: a certificate of 640 products
    (order 16, 32 cells) takes about 2 min.
- **`pos_def`.** It is exact (`ℚ`), so its cost is the size of the rationals. Matching the
  matrix entries (`ext; fin_cases; simp`) dominates beyond about 10×10.

## Optimization tactics
- First-order bounds only, over boxes only; localisation (argmin) is 1D only.

## Roots
- `∃!` for systems needs Krawczyk to contract on the chosen box.

## Tooling and API
- Plain `lake env lean` needs `--load-dynlib` and `--plugin` flags for the C runtime; without them
  tactics give a clear error, but `#eval` gives Lean's own error.
- The double-double type `Interval128` is not used by the tactics; the 128-bit tactics use the
  dyadic `Interval128.Dy` path instead.
- `X.width` is a `Float` (an upper bound, rounded up, used by the search heuristics); the exact
  width is `X.widthRat : Option ℚ`.
- CI on GitHub Actions builds the portable RN+err C backend (runners may lack AVX-512);
  the default local x86_64 build is still AVX-512. The slow Examples and the full axiom
  audit run weekly (or manually), not on every push.
- The showcase repos (em8-realfp, four-body-realfp) are private. Both build unchanged against
  v0.1.0 (em8 `main` and `kernel-only`, four-body `main`); they require realfp by a local path
  next to this repository, not by a pinned git revision.
