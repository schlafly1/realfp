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
- Supported at 128: `interval` goals (`f ≤ c`, `f < c`, `f ∈ Icc a b`, `∧`, `f ≠ c`),
  `root_exists` / `root_unique` (one variable: sign change, for `∃!` a strict derivative sign;
  systems and fallback: Krawczyk with 128-bit interval arithmetic; the preconditioner `Y` is a
  binary64 inverse, so very ill-conditioned Jacobians, condition number near `10¹⁶`, fail),
  `sInf` / `sSup` bounds and witnesses `∃ x ∈ S, f x ≤ c` (128-bit checks; in one variable the
  witness is refined at 128 bits by bisection on the sign of `f'`), argmin/argmax
  localisation in one variable (box width down to about `10⁻¹⁶`, limited by the quadratic value
  gap) and `#realfp_min` / `#realfp_max (precision := 128)` (an untrusted report).
  `integral_bound` and `pos_def` reject it.
- `≠` at 128 is plain bisection (no derivative certificates for exclusion).
- 128-bit for `+ - * / ⁻¹ √ |·| ^n`, rational constants, `π` (Mathlib-proved 40-digit bounds,
  enclosure width about `1e-38`), `exp`, `log`, `sin`, `cos`, `sinh`, `cosh`, `tanh`,
  `logb 2`, `logb 10` (point enclosures about `1e-33` relative; `sin`/`cos` of arguments around
  `10³` about `3e-31`, since the double-angle steps amplify the error). `arctan`, `atan2`, `tan`,
  `arcsin`, `arccos`, registered functions, and `log` / `logb` on intervals not known to be
  positive are evaluated with Interval64 precision (about `1e-16` relative); the failure message
  lists them.
- Kernel cost of the elementary functions: about 0.1–0.4 s per point evaluation (`exp`, `log`,
  `sinh`, …; `sin`/`cos` together about 0.4–0.7 s), and an interval needs two (`exp`, `log`,
  hyperbolic: both endpoints) or one (`sin`/`cos`: centre plus a Lipschitz radius, so wide
  intervals are coarse).
- Derivative certificates at 128 (`Interval128.Dy.DCert`: bisection, monotonicity with the sign
  of `∂ᵢf` proved recursively up to `order`, centred form at the midpoint) mirror Interval64's
  one-variable-at-a-time `DCert`; the multivariate centred forms (`MCert`), Taylor and
  Bernstein certificates of precision 64 are not available at 128. Registered (extension)
  functions are never differentiated at 128.
- Kernel cost of transcendental boxes: a monotonicity step on `sin x + cos x` costs about 1.1 s
  (derivative and endpoint values), so a tight bound at an interior maximum (30 splits, 36
  monotonicity steps for a `1e-16` margin) takes about 55 s in the kernel.
- Kernel cost: about 10–30 ms per box with the dyadic `Nat`/`Int` path (a one-variable bound
  with 60–100 boxes takes about 1 s). Boxes are still plain bisection, so wide boxes with tight
  margins need many of them. The double-double `Interval128` type and its proved checker
  (`Interval128.Refl`) remain in the library, but the tactic no longer uses them.

## Optimization tactics
- First-order bounds only, over boxes only; localisation (argmin) is 1D only.

## Roots
- `∃!` for systems needs Krawczyk to contract on the chosen box.

## Tooling and API
- Plain `lake env lean` needs `--load-dynlib` and `--plugin` flags for the C runtime; without them
  tactics give a clear error, but `#eval` gives Lean's own error.
- The `Interval128` type name is unchanged (`Interval128.Interval128`).
- `X.width` is still a `Float`.
- CI on GitHub Actions builds the portable RN+err C backend (runners may lack AVX-512);
  the default local x86_64 build is still AVX-512. The slow Examples and the full axiom
  audit run weekly (or manually), not on every push.
- The showcase repos (em8-realfp, four-body-realfp) have not been rebuilt against the new API;
  the old type-name alias is kept for them.
