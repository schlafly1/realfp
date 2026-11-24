#!/usr/bin/env bash
# Axiom audit of every RealFP.* theorem (built into the default `lake build` target as
# RealFPMathlib.AxiomAudit; this script just rebuilds and prints that module's report).
set -euo pipefail
cd "$(dirname "$0")/.."
touch RealFPMathlib/AxiomAudit.lean
lake build RealFPMathlib.AxiomAudit -v 2>&1 | grep -E "axiom audit|error" || true
lake build RealFPMathlib.AxiomAudit >/dev/null
