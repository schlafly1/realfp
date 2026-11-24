# The philosophy behind RealFP

*Roger Schlafly*

## Mathematics is finitary

A central aim of mathematics is to give finite proofs about infinite objects. The tradition goes
back to Euclid, who proved that there are infinitely many primes and that every right triangle
satisfies the Pythagorean theorem. Those theorems are about infinitely many objects, yet each
proof uses finitely many symbols and finitely many steps.

Today the most widely used system for formalizing such proofs is Lean 4, together with its
Mathlib library. Lean is finitary too: a Lean proof is a finite object that a small kernel
checks mechanically. Its logic is strong enough to express essentially all of mainstream
mathematics.

## Computers excel at number crunching

For decades, computers have been designed largely for fast floating-point arithmetic. A
common misconception is that such arithmetic is only approximate, and so it has no place in a
rigorous proof. That is wrong, for three reasons.

1. **Floating point is precisely specified.** Since the IEEE 754 standard of 1985, the
   result of every basic operation (add, subtract, multiply, divide, square root) has been
   defined exactly: it is the true result, rounded to a representable number by a stated rule.
   The standard also provides directed rounding (toward −∞ and toward +∞), so a computer can
   produce a number guaranteed to be at most, or at least, the true value.
2. **Approximations can prove exact theorems.** If a computation encloses a quantity in an
   interval that excludes zero, the quantity is not zero, and that is an exact statement.
   Rigorous numerics of this kind were essential to Hales's proof of the Kepler conjecture (formally
   verified by the Flyspeck project in 2014), Tucker's proof that the Lorenz attractor exists
   (2002), and the verification that the first 10¹³ or so nontrivial zeros of the Riemann zeta
   function lie on the critical line.
3. **Exact inputs can give exact outputs.** When the true result of an operation is
   representable, a correctly rounded operation returns it exactly. Integer and dyadic
   computations within range are therefore exact.

## Lean excels at logic

Much of real analysis needs little number crunching. To prove that the product of two
continuous real functions is continuous, you prove a statement about infinitely many numbers,
but you do almost no arithmetic. The proof is a finite sequence of logical steps, and Lean is
designed to formalize exactly that kind of reasoning.

## RealFP is designed for provable number crunching

Lean was not designed for floating-point proofs. Its `Float` type runs on the hardware, but the
kernel treats it as opaque, so nothing can be proved about a `Float` computation. Rocq
(formerly Coq), which Lean has overtaken in popularity for formalizing mathematics, has
primitive floats in its kernel and mature libraries for rigorous numerics such as Flocq and
CoqInterval. Lean has had nothing comparable.

RealFP fills that gap. It implements interval arithmetic on IEEE binary64 numbers with
directed rounding, so every operation returns an interval that provably contains the exact
real result. The operations are defined in Lean and proved correct against Mathlib's real
numbers, and at run time they use the processor's hardware rounding. The aim is to make Lean
practical for proofs that need serious computation with real numbers.

## The trust model

Every proof rests on a trust model: axioms, rules of inference, and a checker. Lean's standard
model is its kernel plus three axioms: `propext`, `Classical.choice` and `Quot.sound`. Mathlib
proves a great deal of textbook mathematics in that model. But any computer proof also trusts
the processor, the memory and the software that runs the checker. A kernel check with
`decide` runs on the same hardware as everything else.

`native_decide` differs in what software it trusts. Instead of having the kernel evaluate a
computation step by step, it compiles the computation to machine code, runs it, and accepts
the answer through the axiom `Lean.ofReduceBool`. That adds trust in the Lean compiler, the C
compiler and any code attached with `@[implemented_by]` or `@[extern]`. For RealFP, that code
is a small C runtime that has to agree with the Lean definitions it replaces.

Lean purists prefer `decide`, as if `native_decide` were inherently less trustworthy. In
practice, `native_decide` uses the computer the way it was designed and tested to be used, and
its results are reliable. The extra trust in the compiler and runtime is real, but small.

RealFP supports both. `trust := kernel` is the default: certificates are checked by the kernel
and use only the three standard axioms. `trust := native` uses `native_decide` and the
hardware C runtime, which makes large computations dramatically faster. That is a slightly
larger trust base, but it amounts to trusting the processor to do arithmetic the way it was
built to. An axiom audit in the default build lists every theorem that relies on native
evaluation.

## The limits of the Hilbert program

In the 1920s, David Hilbert proposed a program to formalize all of mathematics and to prove its
consistency by finitary means. The formalization half was largely achieved, and set theory
settled into the axioms now called ZFC. The consistency half was not. In 1931 Kurt Gödel
showed that any consistent, effectively axiomatized system strong enough for basic arithmetic,
ZFC included, cannot prove its own consistency.

Lean is subject to the same limit: it cannot prove its own consistency. Lean's kernel has been
modeled in Lean, and independent checkers can recheck Lean proofs, but in the end the kernel is
trusted because of the care that went into it and the hardware it runs on. In that light, it is
reasonable to trust your computer to add correctly. If it does not, many other things will go
wrong too.
