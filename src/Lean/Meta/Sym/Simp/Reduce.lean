/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Sym.Reduce
import Lean.Meta.Sym.InferType
namespace Lean.Meta.Sym.Simp

/-!
# Definitional reduction simprocs

`Sym.simp` versions of the reduction steps in `Lean.Meta.Sym.Reduce`. The proof of each step
is `Eq.refl` of the result, which the kernel accepts because the terms are definitionally equal.
-/

/-- Turns the result of a `Sym.Reduce` step into a simproc result. -/
def ofReduce? (r : Option Expr) : SymM Result := do
  let some e' := r | return .rfl
  return .step e' (← mkEqRefl e')

/-- Beta-reduces applications with a lambda head. -/
public def beta : Simproc := fun e => do
  ofReduce? (← reduceBeta? e)

/-- Zeta-reduces `let`/`have` telescopes. -/
public def zeta : Simproc := fun e => do
  ofReduce? (← reduceZeta? e)

/-- Unfolds the let-bound free variables in `s` at head position. -/
public def zetaDelta (s : FVarIdSet) : Simproc := fun e => do
  ofReduce? (← reduceZetaDelta? e s.contains)

/-- Unfolds every let-bound free variable at head position. -/
public def zetaDeltaAll : Simproc := fun e => do
  ofReduce? (← reduceZetaDelta? e)

/-- Reduces projection functions applied to constructors. -/
public def reduceProj : Simproc := fun e => do
  ofReduce? (← reduceProjApp? e)

/-- Iota-reduces `match` and recursor applications whose discriminants are constructors. -/
public def reduceMatcher : Simproc := fun e => do
  ofReduce? (← reduceMatcherApp? e)

end Lean.Meta.Sym.Simp
