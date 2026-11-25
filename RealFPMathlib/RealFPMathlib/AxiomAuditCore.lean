/-
Core axiom audit, plus the short showcase examples in `docs/EXAMPLES.md`.

The default `lake build` still elaborates `RealFPMathlib.AxiomAudit`, which imports every
module including the slower feature examples. This file is the same check over the library,
Demo, Tests and the polished showcases, so the push CI can audit axioms without
building the slow example files.

Run: `lake build RealFPMathlib.AxiomAuditCore`
-/
import RealFPMathlib
import RealFPMathlib.Asin
import RealFPMathlib.Basic
import RealFPMathlib.Bern
import RealFPMathlib.Conv
import RealFPMathlib.Corners
import RealFPMathlib.Demo
-- Polished showcase examples (each compiles in well under 30 s).
import RealFPMathlib.Examples.AMGM
import RealFPMathlib.Examples.Constants
import RealFPMathlib.Examples.ExpPi
import RealFPMathlib.Examples.Gaussian
import RealFPMathlib.Examples.Jordan
import RealFPMathlib.Examples.LogIneq
import RealFPMathlib.Examples.Motzkin
import RealFPMathlib.Ext
import RealFPMathlib.Extensions.Arsinh
import RealFPMathlib.Extensions.Artanh
import RealFPMathlib.Extensions.Erf
import RealFPMathlib.Extensions.Sinc
import RealFPMathlib.Front
import RealFPMathlib.Hyp
import RealFPMathlib.I128DD
import RealFPMathlib.I128Mem
import RealFPMathlib.I128Prims
import RealFPMathlib.I128Sound
import RealFPMathlib.I128DyBase
import RealFPMathlib.I128DyTransc
import RealFPMathlib.I128Dyadic
import RealFPMathlib.I128Deriv
import RealFPMathlib.I128Roots
import RealFPMathlib.I128Kraw
import RealFPMathlib.PiBounds
import RealFPMathlib.IntegralTactic
import RealFPMathlib.IntervalDeriv
import RealFPMathlib.IntervalSound
import RealFPMathlib.IntervalTactic
import RealFPMathlib.InvTrig
import RealFPMathlib.KMatrix
import RealFPMathlib.KQuad
import RealFPMathlib.KQuadShare
import RealFPMathlib.KTaylor2
import RealFPMathlib.Krawczyk
import RealFPMathlib.Matrix
import RealFPMathlib.MatrixPD
import RealFPMathlib.Mem
import RealFPMathlib.Ops
import RealFPMathlib.Poly
import RealFPMathlib.PosDefTactic
import RealFPMathlib.PosDefQ
import RealFPMathlib.I128TM
import RealFPMathlib.I128TMF
import RealFPMathlib.Pow
import RealFPMathlib.Quad
import RealFPMathlib.Quad2
import RealFPMathlib.Registry
import RealFPMathlib.RootTactic
import RealFPMathlib.Roots
import RealFPMathlib.Split
import RealFPMathlib.Tan
import RealFPMathlib.Taylor2
import RealFPMathlib.TaylorBound
import RealFPMathlib.Tests.IntervalTest
import RealFPMathlib.Tests.KernelNativeAgree
import RealFPMathlib.Tests.TouchTest
import RealFPMathlib.Tight
import RealFPMathlib.Transc
import RealFPMathlib.Trig
import RealFPMathlib.Trust
import RealFPMathlib.Unbounded

open Lean Elab Command

namespace RealFP.AxiomAuditCore

abbrev Memo := Std.HashMap Name NameSet

/-- Axioms a constant depends on (memoised over the whole environment). -/
partial def axiomsOf (env : Environment) (n : Name) : StateM Memo NameSet := do
  if let some s := (← get)[n]? then return s
  modify (·.insert n {})  -- cycle guard
  let some ci := env.find? n | return {}
  let mut acc : NameSet := {}
  if ci matches .axiomInfo _ then acc := acc.insert n
  let body : Option Expr := match ci with
    | .defnInfo v => some v.value
    | .thmInfo v => some v.value
    | .opaqueInfo v => some v.value
    | _ => none
  let refs := ci.type.getUsedConstants ++ (body.map (·.getUsedConstants)).getD #[]
  let refs := match ci with
    | .inductInfo v => refs ++ v.ctors.toArray
    | .ctorInfo v => refs.push v.induct
    | .recInfo v => refs.push v.getMajorInduct
    | _ => refs
  for r in refs do
    for a in (← axiomsOf env r) do acc := acc.insert a
  modify (·.insert n acc)
  return acc

def standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def isNative (a : Name) : Bool :=
  a == `Lean.ofReduceBool || a == `Lean.trustCompiler ||
    a.components.any fun c => c == `_native

elab "#realfp_audit_axioms_core" : command => do
  let env ← getEnv
  let mut memo : Memo := {}
  let mut bad : Array MessageData := #[]
  let mut nThm := 0
  let mut nNative := 0
  for (n, ci) in env.constants.toList do
    unless (`RealFP).isPrefixOf n do continue
    if n.isInternal then continue
    unless ci matches .thmInfo _ do continue
    nThm := nThm + 1
    let (ax, m) := (axiomsOf env n).run memo
    memo := m
    let nativeOK := (`RealFP.Demo).isPrefixOf n || (`RealFP.Examples).isPrefixOf n
    let extra := ax.toList.filter fun a => !standard.contains a
    if extra.any isNative then nNative := nNative + 1
    let disallowed := extra.filter fun a => !(nativeOK && isNative a)
    unless disallowed.isEmpty do
      bad := bad.push m!"{n}: {disallowed}"
  if bad.isEmpty then
    logInfo m!"axiom audit passed (core + showcases, no slow Examples): {nThm} RealFP theorems; {nNative} (Demo/Examples only) use \
      native_decide, all others only propext, Classical.choice, Quot.sound"
  else
    throwError m!"axiom audit FAILED for {bad.size} theorem(s):\n{MessageData.joinSep bad.toList "\n"}"

#realfp_audit_axioms_core

end RealFP.AxiomAuditCore
