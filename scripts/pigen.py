from fractions import Fraction as F
import math, sys
PI = F("3.141592653589793238462643383279502884197169399375105820974944592307816406286")
def ceil_to(x, P):  # round up to multiple of 2^-P
    return F(-((-x.numerator * 2**P) // x.denominator), 2**P)
def floor_to(x, P):
    return F((x.numerator * 2**P) // x.denominator, 2**P)
def lower(a, n, extra=140):
    # need r_k = 2 - e_k, e_n >= T=(a/2^(n+1))^2, e_k >= 4 e_{k+1} - e_{k+1}^2, e_0 = 2 (r_0=0)
    T = (a / 2**(n+1))**2
    e = [None]*(n+1); e[n] = ceil_to(T, 2*n+extra)
    for k in range(n-1, 0, -1):
        e[k] = ceil_to(4*e[k+1] - e[k+1]**2, 2*k+extra)
    req0 = 4*e[1] - e[1]**2
    assert req0 <= 2, ("insufficient", float(req0-2))
    rs = [2 - e[k] for k in range(1, n+1)]
    # verify conditions as mathlib checks: (2*b + a)*d^2 <= c^2*b for prev a/b, new c/d
    prev = F(0)
    for r in rs:
        assert (2 + prev) <= r*r, "step"
        prev = r
    assert prev <= 2 - T
    return rs
def upper(a, n, extra=140):
    T = ((a - F(1, 4**n)) / 2**(n+1))**2
    e = [None]*(n+1); e[n] = floor_to(T, 2*n+extra)
    for k in range(n-1, 0, -1):
        e[k] = floor_to(4*e[k+1] - e[k+1]**2, 2*k+extra)
    req0 = 4*e[1] - e[1]**2
    assert req0 >= 2, ("insufficient", float(req0-2))
    rs = [2 - e[k] for k in range(1, n+1)]
    prev = F(0)
    for r in rs:
        assert r*r <= 2 + prev and r >= 0, "step"
        prev = r
    assert 2 - T <= prev
    return rs
D = int(sys.argv[1]); n = int(sys.argv[2])
lo = F(math.floor(PI * 10**D), 10**D); hi = lo + F(1, 10**D)
def fmt(rs):
    out=[]
    for r in rs:
        if r > 1: out.append(f"2-{(2-r).numerator}/{(2-r).denominator}")
        else: out.append(f"{r.numerator}/{r.denominator}")
    return ",\n    ".join(out)
L = lower(lo, n); U = upper(hi, n)
print(f"-- lo = {lo.numerator}/{lo.denominator}")
print(f"theorem pi_gt_d{D} : ({lo.numerator} / {lo.denominator} : ℝ) < π := by\n  pi_lower_bound [\n    {fmt(L)}]\n")
print(f"theorem pi_lt_d{D} : π < ({hi.numerator} / {hi.denominator} : ℝ) := by\n  pi_upper_bound [\n    {fmt(U)}]")
