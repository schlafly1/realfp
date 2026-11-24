#!/usr/bin/env python3
"""Check that every line of every ```lean block in TUTORIAL.md (except the lakefile example)
occurs in RealFPMathlib/RealFPMathlib/Examples/Tutorial.lean (or, for the "Adding a function"
section, RealFPMathlib/Extensions/*.lean and the matching Examples), which the default build compiles.
Trailing `-- comments` and comment-only lines are ignored. Run from the repository root.
Looks for docs/TUTORIAL.md, then TUTORIAL.md at the repo root.
"""
import glob, os, re, sys
md_path = next((p for p in ('docs/TUTORIAL.md', 'TUTORIAL.md') if os.path.exists(p)), None)
if md_path is None:
    print('TUTORIAL.md not found (tried docs/TUTORIAL.md and TUTORIAL.md)')
    sys.exit(1)
md = open(md_path).read()
ext = sorted(glob.glob('RealFPMathlib/RealFPMathlib/Extensions/*.lean'))  # "Adding a function"
lean = '\n'.join(open(p).read() for p in
    ['RealFPMathlib/RealFPMathlib/Examples/Tutorial.lean'] + ext +
    ['RealFPMathlib/RealFPMathlib/Examples/' + os.path.basename(p) for p in ext])
strip = lambda l: re.sub(r'\s+--.*$', '', l).strip()
have = {strip(l) for l in lean.splitlines()}
missing = [t for b in re.findall(r'```lean\n(.*?)```', md, re.S) if 'import Lake' not in b
           for t in map(strip, b.splitlines()) if t and not t.startswith('--') and t not in have]
for t in missing: print('not in Tutorial.lean:', t)
print('ok' if not missing else f'{len(missing)} missing line(s) ({md_path})')
sys.exit(1 if missing else 0)
