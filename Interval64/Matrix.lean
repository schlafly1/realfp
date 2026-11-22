/-
Rigorous positive-definiteness certificates for interval matrices.

An `IMat` is an `n × n` matrix of `Interval64` entries, stored row-major as two
`FloatArray`s (`lo`, `hi`). The certificate is a congruence followed by a
Gershgorin test:

1. `approxX M` (plain round-to-nearest floating point, **not trusted**): a lower-triangular
   `X ≈ L⁻¹` from a Cholesky factorisation `mid M ≈ L Lᵀ`.
2. `pdMargins M X` (directed rounding, the trusted part): interval enclosures of
   `B = X A Xᵀ` for every symmetric `A` in the box (only the lower triangle is computed;
   `B` is symmetric), and of the Gershgorin margins `r i = B i i - Σ_{l ≠ i} |B i l|`.
3. `pdCheck M X`: every used `X` entry is finite and every margin has `0 < lo`.

If `pdCheck M X = true` then every real symmetric `A` with `A i j ∈ M i j` is positive
definite (`RealFP.Mat.posDef_of_pdCheck`): `B` is strictly diagonally dominant with a
positive diagonal, so `B` is positive definite, so `X` is invertible and `A` is too.
`X` can be any matrix; a poor `X` only makes the check fail.

`pdMargins` (`O(n³)`) has a C implementation (`iv64_pd_margins`, `c/iv64_matrix.c`)
attached with `@[implemented_by]`; it performs exactly the same `Interval64`
operations in the same order (bit-identical; checked by the test executable).
Everything else is plain Lean.

Derived checks: `lamMinCheck M X s` (`A - s I` positive definite, i.e. `λ_min(A) > s`),
`gtCheck M N X` (`A - B` positive definite, i.e. `A > B` in the Loewner order).
-/
import Interval64.Ops
import Interval64.Conv

namespace Interval64

/-- Total `FloatArray` read: `0` outside the array. -/
@[inline] def fget (a : FloatArray) (k : Nat) : Float := if h : k < a.size then a[k] else 0

/-- `FloatArray` of length `m` with entries `f k`. -/
def FloatArray.ofFn (m : Nat) (f : Nat → Float) : FloatArray :=
  ⟨Array.ofFn (n := m) fun k => f k.val⟩

namespace Mat

/-- `[0, 0]`. -/
def zeroI : Interval64 := ⟨0, 0⟩

/-- Interval dot product `Σ_{k < len} f k * g k`, accumulated left to right from `[0, 0]`. -/
def idot (f g : Nat → Interval64) : Nat → Interval64
  | 0 => zeroI
  | k + 1 => idot f g k + f k * g k

/-- Interval sum `Σ_{k < len, k ≠ skip} f k`, left to right from `[0, 0]`. -/
def isumSkip (f : Nat → Interval64) (skip : Nat) : Nat → Interval64
  | 0 => zeroI
  | k + 1 => if k = skip then isumSkip f skip k else isumSkip f skip k + f k

end Mat

/-- An `n × n` interval matrix, row-major: entry `(i, j)` is `[lo[i*n+j], hi[i*n+j]]`
    (missing array entries read as `0`). -/
structure IMat where
  n : Nat
  lo : FloatArray
  hi : FloatArray
  deriving Inhabited

namespace IMat

/-- Entry `(i, j)`. -/
def get (M : IMat) (i j : Nat) : Interval64 := ⟨fget M.lo (i * M.n + j), fget M.hi (i * M.n + j)⟩

/-- Build from an entry function. -/
def ofFn (n : Nat) (f : Nat → Nat → Interval64) : IMat :=
  ⟨n, FloatArray.ofFn (n * n) (fun k => (f (k / n) (k % n)).lo),
      FloatArray.ofFn (n * n) (fun k => (f (k / n) (k % n)).hi)⟩

/-- Point matrix of a `Float` matrix (row-major). -/
def ofFloats (n : Nat) (a : FloatArray) : IMat := ⟨n, a, a⟩

/-- Entrywise `M - N` (size of `M`). -/
def sub (M N : IMat) : IMat := ofFn M.n fun i j => M.get i j - N.get i j

/-- `M - s I`. -/
def subDiag (M : IMat) (s : Float) : IMat :=
  ofFn M.n fun i j => if i = j then M.get i j - point s else M.get i j

/-- Midpoint matrix (round to nearest; untrusted helper). -/
def midF (M : IMat) : FloatArray :=
  FloatArray.ofFn (M.n * M.n) fun k => 0.5 * fget M.lo k + 0.5 * fget M.hi k

end IMat

namespace Mat

/-- Point interval of `X[i, j]`. -/
def xent (n : Nat) (X : FloatArray) (i j : Nat) : Interval64 := point (fget X (i * n + j))

/-- `T i k = Σ_{j ≤ i} X i j * A j k` (`X` lower triangular). -/
def tEntry (M : IMat) (X : FloatArray) (i k : Nat) : Interval64 :=
  idot (fun j => xent M.n X i j) (fun j => M.get j k) (i + 1)

/-- All of `T`, row-major. -/
def tArr (M : IMat) (X : FloatArray) : Array Interval64 :=
  Array.ofFn (n := M.n * M.n) fun k => tEntry M X (k.val / M.n) (k.val % M.n)

/-- `B i l = Σ_{k ≤ l} T i k * X l k` for `l ≤ i` (`B = X A Xᵀ`). -/
def bEntry (M : IMat) (X : FloatArray) (T : Array Interval64) (i l : Nat) : Interval64 :=
  idot (fun k => T.getD (i * M.n + k) zeroI) (fun k => xent M.n X l k) (l + 1)

/-- Lower triangle of `B` (row-major; `[0, 0]` above the diagonal). -/
def bArr (M : IMat) (X : FloatArray) : Array Interval64 :=
  let T := tArr M X
  Array.ofFn (n := M.n * M.n) fun k =>
    if k.val % M.n ≤ k.val / M.n then bEntry M X T (k.val / M.n) (k.val % M.n) else zeroI

/-- `B i l` read from the lower triangle (symmetric). -/
def bget (n : Nat) (B : Array Interval64) (i l : Nat) : Interval64 :=
  if l ≤ i then B.getD (i * n + l) zeroI else B.getD (l * n + i) zeroI

/-- Gershgorin margin `B i i - Σ_{l ≠ i} |B i l|`. -/
def margin (n : Nat) (B : Array Interval64) (i : Nat) : Interval64 :=
  bget n B i i - isumSkip (fun l => Interval64.abs (bget n B i l)) i n

/-- Margins as `[lo₀, hi₀, lo₁, hi₁, …]` (specification). -/
def pdMarginsSpec (M : IMat) (X : FloatArray) : FloatArray :=
  let B := bArr M X
  FloatArray.ofFn (2 * M.n) fun k =>
    let r := margin M.n B (k / 2)
    if k % 2 = 0 then r.lo else r.hi

/-- C implementation of `pdMarginsSpec` (`c/iv64_matrix.c`). -/
@[extern "iv64_pd_margins"]
opaque pdMarginsImpl (M : @& IMat) (X : @& FloatArray) : FloatArray

/-- Gershgorin margins of `X A Xᵀ` (Lean spec; C at runtime). -/
@[implemented_by pdMarginsImpl]
def pdMargins (M : @& IMat) (X : @& FloatArray) : FloatArray := pdMarginsSpec M X

/-- Every entry `X i j` with `j ≤ i < n` is finite. -/
def xFinite (n : Nat) (X : FloatArray) : Bool :=
  (List.range n).all fun i => (List.range (i + 1)).all fun j =>
    let x := fget X (i * n + j)
    !x.isNaN && !x.isInf

/-- Every margin lower bound is `> 0`. -/
def marginsPos (n : Nat) (m : FloatArray) : Bool :=
  (List.range n).all fun i => decide (0 < fget m (2 * i))

/-- Positive-definiteness certificate check for the interval matrix `M` with the
    (untrusted) congruence `X`. -/
def pdCheck (M : IMat) (X : FloatArray) : Bool :=
  xFinite M.n X && marginsPos M.n (pdMargins M X)

/-! ### The untrusted congruence `X ≈ L⁻¹` -/

/-- Cholesky `a ≈ L Lᵀ` of a row-major `n × n` float matrix (lower triangle of the result;
    NaN if a pivot is not positive). Round to nearest; untrusted. -/
def cholF (n : Nat) (a : FloatArray) : FloatArray := Id.run do
  let mut L : FloatArray := FloatArray.ofFn (n * n) fun _ => 0
  for j in [0:n] do
    let mut s := fget a (j * n + j)
    for k in [0:j] do
      let v := fget L (j * n + k)
      s := s - v * v
    let d := if s > 0 then s.sqrt else Float.nan
    L := L.set! (j * n + j) d
    for i in [j+1:n] do
      let mut t := fget a (i * n + j)
      for k in [0:j] do
        t := t - fget L (i * n + k) * fget L (j * n + k)
      L := L.set! (i * n + j) (t / d)
  return L

/-- Inverse of a lower-triangular row-major float matrix (forward substitution; untrusted). -/
def lowerInvF (n : Nat) (L : FloatArray) : FloatArray := Id.run do
  let mut X : FloatArray := FloatArray.ofFn (n * n) fun _ => 0
  for j in [0:n] do
    X := X.set! (j * n + j) (1 / fget L (j * n + j))
    for i in [j+1:n] do
      let mut t : Float := 0
      for k in [j:i] do
        t := t + fget L (i * n + k) * fget X (k * n + j)
      X := X.set! (i * n + j) (-t / fget L (i * n + i))
  return X

/-- Default congruence: `X = L⁻¹` with `mid M ≈ L Lᵀ` (untrusted). -/
def approxX (M : IMat) : FloatArray := lowerInvF M.n (cholF M.n M.midF)

/-- `pdCheck` with the default congruence. -/
def isPD (M : IMat) : Bool := pdCheck M (approxX M)

/-- Certificate that `λ_min(A) > s` for every symmetric `A ∈ M`: `A - s I` is positive definite. -/
def lamMinCheck (M : IMat) (X : FloatArray) (s : Float) : Bool :=
  !s.isNaN && !s.isInf && pdCheck (M.subDiag s) X

/-- `lamMinCheck` with the default congruence. -/
def lamMinGt (M : IMat) (s : Float) : Bool :=
  lamMinCheck M (approxX (M.subDiag s)) s

/-- Certificate that `A - B` is positive definite for all symmetric `A ∈ M`, `B ∈ N`. -/
def gtCheck (M N : IMat) (X : FloatArray) : Bool := pdCheck (M.sub N) X

/-- `gtCheck` with the default congruence. -/
def isGt (M N : IMat) : Bool := gtCheck M N (approxX (M.sub N))

end Mat
end Interval64
