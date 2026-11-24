# Known limitations

Current as of commit `3d051fa` (November 2026). These are known gaps, not bugs in soundness:
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

## Optimization tactics
- First-order bounds only, over boxes only; localisation (argmin) is 1D only.

## Roots
- `∃!` for systems needs Krawczyk to contract on the chosen box.

## Tooling and API
- Plain `lake env lean` needs `--load-dynlib` and `--plugin` flags for the C runtime; without them
  tactics give a clear error, but `#eval` gives Lean's own error.
- The `Interval128` type name is unchanged, and `Interval128` is not yet used inside the tactics.
- `X.width` is still a `Float`.
- CI on GitHub Actions builds the portable RN+err C backend (runners may lack AVX-512);
  the default local x86_64 build is still AVX-512. The slow Examples and the full axiom
  audit run weekly (or manually), not on every push.
- The showcase repos (em8-realfp, four-body-realfp) have not been rebuilt against the new API;
  the old type-name alias is kept for them.
