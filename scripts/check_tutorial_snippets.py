#!/usr/bin/env python3
"""Check that every line of every ```lean block in TUTORIAL.md (except the lakefile example)
occurs in RealFPMathlib/RealFPMathlib/Examples/Tutorial.lean, which the default build compiles.
Trailing `-- comments` and comment-only lines are ignored. Run from the repository root."""
import re, sys
md = open('TUTORIAL.md').read()
lean = open('RealFPMathlib/RealFPMathlib/Examples/Tutorial.lean').read()
strip = lambda l: re.sub(r'\s+--.*$', '', l).strip()
have = {strip(l) for l in lean.splitlines()}
missing = [t for b in re.findall(r'```lean\n(.*?)```', md, re.S) if 'import Lake' not in b
           for t in map(strip, b.splitlines()) if t and not t.startswith('--') and t not in have]
for t in missing: print('not in Tutorial.lean:', t)
print('ok' if not missing else f'{len(missing)} missing line(s)')
sys.exit(1 if missing else 0)
