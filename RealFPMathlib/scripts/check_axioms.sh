#!/usr/bin/env bash
# Axiom report for the Mathlib layer: every theorem may use only propext,
# Classical.choice, Quot.sound; native_decide axioms only in RealFP.Demo.*.
set -euo pipefail
here="$(cd "$(dirname "$0")/.." && pwd)"
NATIVE_ONLY_IN='RealFP\.Demo\.' exec "$here/../scripts/check_axioms.sh" RealFPMathlib RealFPMathlibAxioms.lean
