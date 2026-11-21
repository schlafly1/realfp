#!/usr/bin/env python3
"""Generate tests/func_oracle.txt: correctly rounded RD/RU values of the CORE-MATH
functions beyond exp/log/sin/cos (atan, atan2, ...), computed with mpmath at 2500
bits. Line format: `fn arg1_bits [arg2_bits] RD_bits RU_bits` (`nan nan` = NaN).
Two-argument functions use C argument order (`atan2 y x`).

    python3 scripts/gen_func_oracle.py SEED COUNT [fn ...] > tests/func_oracle.txt
"""
import random, struct, mpmath, math, sys
mpmath.mp.prec = 2500
def f2u(x): return struct.unpack('<Q', struct.pack('<d', x))[0]
def u2f(u): return struct.unpack('<d', struct.pack('<Q', u))[0]
INF = math.inf
MAXF = 1.7976931348623157e308
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
count = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
fns = sys.argv[3:] or ['atan', 'atan2', 'tan', 'asin', 'acos', 'sinh', 'cosh', 'tanh', 'log2', 'log10', 'pow']
random.seed(seed)
PI = mpmath.pi

def rnd(y):
  """(RD, RU) of a real mpf y."""
  if y == 0: return (0.0, 0.0)
  try: f = float(y)
  except OverflowError: f = INF if y > 0 else -INF
  if math.isinf(f):
    return (MAXF, INF) if f > 0 else (-INF, -MAXF)
  F = mpmath.mpf(f)
  # exact results (e.g. log10(1000), pow(4, 0.5)) come out within 2^-2400 relative at 2500 bits;
  # inexact ones are never that close to a double
  if F == y or (F != 0 and abs(y - F) <= abs(F) * mpmath.mpf(2) ** -2400): return (f, f)
  if F > y: return (math.nextafter(f, -INF), f)
  return (f, math.nextafter(f, INF))

def sgn0(v):  # signed zero result
  return (v, v)

def atan(x):
  if math.isnan(x): return None
  if x == 0: return sgn0(x)
  if math.isinf(x): return rnd(PI / 2 if x > 0 else -PI / 2)
  return rnd(mpmath.atan(mpmath.mpf(x)))

def atan2(y, x):
  if math.isnan(x) or math.isnan(y): return None
  neg = math.copysign(1.0, y) < 0
  s = -1 if neg else 1
  if y == 0:
    if math.copysign(1.0, x) > 0: return sgn0(y)          # +0 or x > 0
    return rnd(s * PI)                                      # -0 or x < 0
  if math.isinf(y):
    if math.isinf(x): return rnd(s * (PI / 4 if x > 0 else 3 * PI / 4))
    return rnd(s * PI / 2)
  if x == 0: return rnd(s * PI / 2)
  if math.isinf(x):
    return sgn0(math.copysign(0.0, y)) if x > 0 else rnd(s * PI)
  return rnd(mpmath.atan2(mpmath.mpf(y), mpmath.mpf(x)))

def one(fn, x):
  if math.isnan(x): return None
  X = mpmath.mpf(x) if not math.isinf(x) else None
  if fn == 'tan':
    if math.isinf(x): return None
    if x == 0: return sgn0(x)
    return rnd(mpmath.tan(X))
  if fn in ('asin', 'acos'):
    if math.isinf(x) or abs(x) > 1: return None
    if fn == 'asin':
      if x == 0: return sgn0(x)
      return rnd(mpmath.asin(X))
    if x == 1: return (0.0, 0.0)
    return rnd(mpmath.acos(X))
  if fn == 'sinh':
    if x == 0 or math.isinf(x): return sgn0(x)
    return rnd(mpmath.sinh(X))
  if fn == 'cosh':
    if math.isinf(x): return (INF, INF)
    if x == 0: return (1.0, 1.0)
    return rnd(mpmath.cosh(X))
  if fn == 'tanh':
    if x == 0: return sgn0(x)
    if math.isinf(x): return sgn0(math.copysign(1.0, x))
    r = rnd(mpmath.tanh(X))
    # |tanh x| < 1 for finite x even when 1 - |tanh x| is below the working precision
    if r == (1.0, 1.0): return (math.nextafter(1.0, 0.0), 1.0)
    if r == (-1.0, -1.0): return (-1.0, math.nextafter(-1.0, 0.0))
    return r
  if fn in ('log2', 'log10'):
    if x < 0: return None
    if x == 0: return (-INF, -INF)
    if math.isinf(x): return (INF, INF)
    if x == 1: return (0.0, 0.0)
    return rnd(mpmath.log(X, 2) if fn == 'log2' else mpmath.log10(X))
  raise ValueError(fn)
for _f in ['tan', 'asin', 'acos', 'sinh', 'cosh', 'tanh', 'log2', 'log10']:
  globals()[_f] = (lambda f: (lambda x: one(f, x)))(_f)

def is_int(v): return not math.isinf(v) and v == math.floor(v)
def is_odd(v): return is_int(v) and abs(v) < 2 ** 53 and int(v) % 2 == 1
def pow(x, y):  # C99 F.10.4.4
  if y == 0 or x == 1: return (1.0, 1.0)
  if math.isnan(x) or math.isnan(y): return None
  if math.isinf(y):
    if x == -1: return (1.0, 1.0)
    small = abs(x) < 1
    return (INF, INF) if (small and y < 0) or (not small and y > 0) else (0.0, 0.0)
  if x == 0:
    if y < 0: return (math.copysign(INF, x), math.copysign(INF, x)) if is_odd(y) else (INF, INF)
    return sgn0(x) if is_odd(y) else (0.0, 0.0)
  if math.isinf(x):
    if x > 0: return (INF, INF) if y > 0 else (0.0, 0.0)
    if y < 0: return sgn0(-0.0) if is_odd(y) else (0.0, 0.0)
    return (-INF, -INF) if is_odd(y) else (INF, INF)
  if x < 0 and not is_int(y): return None
  X, Y = mpmath.mpf(x), mpmath.mpf(y)
  r = mpmath.power(abs(X), Y)
  if x < 0 and is_odd(y): r = -r
  return rnd(r)

SPECIAL = [0.0, -0.0, 1.0, -1.0, INF, -INF, math.nan, 5e-324, -5e-324,
           2.2250738585072014e-308, MAXF, -MAXF, 1e-300, 0.5, 2.0, 3.0, 1e22, 1e300,
           1e-8, 1.5e-8, 2**-27, 0.4, 1e16, -1e16, 2**53]
def rand_arg():
  r = random.random()
  if r < 0.4: return random.uniform(-10, 10)
  if r < 0.7: return random.uniform(-1, 1) * 2 ** random.randint(-80, 60)
  return u2f(random.getrandbits(64))

print("# Oracle for CORE-MATH under RD/RU: fn arg_bits... RD_bits RU_bits (nan = NaN expected).")
print(f"# Generated by scripts/gen_func_oracle.py with mpmath at {mpmath.mp.prec} bits; args: {' '.join(sys.argv[1:])}")
def emit(fn, args, o):
  a = ' '.join(f"{f2u(v):016x}" for v in args)
  print(f"{fn} {a} " + ("nan nan" if o is None else f"{f2u(o[0]):016x} {f2u(o[1]):016x}"))
import os
WC = os.environ.get('COREMATH_SRC')  # optional: CORE-MATH src/binary64 dir for worst cases
def hard(fn, n):
  if not WC: return []
  path = os.path.join(WC, fn, fn + '.wc')
  out = []
  for line in open(path):
    line = line.split('#')[0].strip()
    if not line or 'nan' in line: continue
    try: out.append([float.fromhex(t.strip().replace('+inf', 'inf')) for t in line.split(',')])
    except ValueError: pass
  rs = random.Random(seed)
  return rs.sample(out, min(n, len(out)))
for fn in fns:
  for args in hard(fn, count):
    emit(fn, args, globals()[fn](*args))
  if fn == 'atan':
    for x in SPECIAL + [rand_arg() for _ in range(count)]: emit(fn, [x], atan(x))
  elif fn == 'pow':
    for x in SPECIAL[:13] + [-2.0, 4.0, 0.25, 10.0]:
      for y in SPECIAL[:13] + [0.5, -0.5, 3.0, -3.0, 2.0]: emit(fn, [x, y], pow(x, y))
    for _ in range(count):
      x = abs(rand_arg()) if random.random() < 0.7 else rand_arg()
      r = random.random()
      if r < 0.3: y = random.uniform(-30, 30)
      elif r < 0.5: y = float(random.randint(-40, 40))
      elif r < 0.6: y = random.uniform(-1, 1) * 2 ** random.randint(-40, 0)
      else: y = rand_arg()
      if r >= 0.6 and random.random() < 0.8: x = random.uniform(0.5, 2)
      emit(fn, [x, y], pow(x, y))
    for k in range(-5, 25):
      emit(fn, [10.0, float(k)], pow(10.0, float(k)))
  elif fn in ('tan', 'asin', 'acos', 'sinh', 'cosh', 'tanh', 'log2', 'log10'):
    f = globals()[fn]
    xs = SPECIAL + [rand_arg() for _ in range(count)]
    if fn in ('asin', 'acos'): xs += [random.uniform(-1, 1) for _ in range(count)]
    if fn in ('sinh', 'cosh', 'tanh'): xs += [random.uniform(-720, 720) for _ in range(count // 2)]
    if fn in ('log2', 'log10'): xs += [abs(v) for v in xs[:count]] + [2.0 ** k for k in range(-1074, 1024, 37)] + [10.0 ** k for k in range(0, 23)]
    for x in xs: emit(fn, [x], f(x))
  elif fn == 'atan2':
    for y in SPECIAL[:13]:
      for x in SPECIAL[:13]: emit(fn, [y, x], atan2(y, x))
    for _ in range(count):
      y, x = rand_arg(), rand_arg()
      if random.random() < 0.2: x = -abs(x)
      emit(fn, [y, x], atan2(y, x))
