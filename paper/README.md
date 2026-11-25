# realfp paper

`realfp.tex` + `refs.bib`: a short arXiv-style paper on realfp. Build with `make`
(pdflatex + bibtex; arXiv-compatible packages only) or `latexmk -pdf realfp.tex`.
`realfp.pdf` is the compiled version.

- `snippets/PaperSnippets.lean`: every Lean snippet in the paper; `make snippets`
  checks them (all kernel-checked, standard axioms, except the one `trust := native` demo).
- `bench/`: raw logs and goal files behind the benchmark tables (2026-11-25 unless the
  file name says otherwise; 8-vCPU Xeon VM with AVX-512, Lean/Mathlib v4.36.0, realfp 61f8eef).
  - `kernel-vs-native-*.txt`, `goals-kn/`: Table 1 (`goals-kn/run.sh`).
  - `kernel-whnf-*.log/md`, `KernelCellRealfp.lean`: Table 2 kernel rows, using FloatLib's
    `benchmarks/kernel/Harness.lean` (MIT, not copied here) for both libraries;
    `interval64_bench.log`: compiled rows (`lake exe interval64_bench`);
    `kernel-isdefeq-KF-vs-spec.log`: `bench/KB_kf.lean`.
  - `floatlib-shared-*.txt`, `goals-floatlib/`: FloatLib column of Table 3 (FloatLib d24844f).
    The LeanCert and realfp columns are `experimental/bench/leancert/results-2026-11-23.txt`
    and docs/COMPARISONS.md; `realfp-shared-2026-11-25.txt` is a rerun under machine load.
