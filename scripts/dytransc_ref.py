#!/usr/bin/env python3
"""Reference values (mpmath, 60 digits) for the Interval128 dyadic elementary-function tests
(`Interval128DyTests.lean`). Prints Lean list entries `(fn, x, ref)` with `ref` a 50-digit
decimal rational."""
import mpmath
from fractions import Fraction
mpmath.mp.dps = 60
pts = [Fraction(1), Fraction(-1), Fraction(1, 3), Fraction(-7, 5), Fraction(1, 10**10), Fraction(2),
       Fraction(10), Fraction(-20), Fraction(100), Fraction(1000), Fraction(-12345, 7), Fraction(3, 1024),
       Fraction(1, 10**6), Fraction(25), Fraction(7, 2)]
fns = {"exp": mpmath.exp, "log": mpmath.log, "sin": mpmath.sin, "cos": mpmath.cos,
       "sinh": mpmath.sinh, "cosh": mpmath.cosh, "tanh": mpmath.tanh,
       "log2": lambda x: mpmath.log(x, 2), "log10": lambda x: mpmath.log(x, 10)}
out = []
for f, F in fns.items():
    for p in pts:
        if f.startswith("log") and p <= 0: continue
        if f in ("exp", "sinh", "cosh") and abs(p) > 200: continue
        x = mpmath.mpf(p.numerator) / p.denominator
        v = F(x)
        s = mpmath.nstr(v, 50, min_fixed=-mpmath.inf, max_fixed=mpmath.inf)
        q = Fraction(s)
        out.append(f'  ("{f}", ({p.numerator} : Rat) / {p.denominator}, ({q.numerator} : Rat) / {q.denominator})')
print("def refs : List (String × Rat × Rat) := [\n" + ",\n".join(out) + "]")
