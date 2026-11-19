/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.DSimp.DSimpM
import Lean.Meta.Sym.Reduce
import Lean.Meta.WHNF
namespace Lean.Meta.Sym.DSimp

/-- Turns the result of a `Sym.Reduce` step into a `dsimp` result. -/
def ofReduce? (r : Option Expr) : Result :=
  match r with
  | none => .rfl
  | some e' => .step e'

public def beta : DSimproc := fun e => do
  return ofReduce? (← reduceBeta? e)

/-- Unfolds the let-bound free variables in `s` at head position. See `Sym.reduceZetaDelta?`. -/
public def zetaDelta (s : FVarIdSet) : DSimproc := fun e => do
  return ofReduce? (← reduceZetaDelta? e s.contains)

public def zetaDeltaAll : DSimproc := fun e => do
  return ofReduce? (← reduceZetaDelta? e)

public def zeta : DSimproc := fun e => do
  return ofReduce? (← reduceZeta? e)

public def dsimpProj : DSimproc := fun e => do
  return ofReduce? (← reduceProjApp? e)

public def dsimpMatch : DSimproc := fun e => do
  return ofReduce? (← reduceMatcherApp? e)

/--
Unfolds the applications of the definitions in `declNames`, like `Meta.simp` does for the
definitions provided in `simp [f]`. A definition with smart unfolding support is unfolded only
when its recursion argument reduces. Any other definition is unfolded only when applied to at
least as many arguments as its number of leading lambdas.
-/
public def unfold (declNames : NameSet) : DSimproc := fun e => do
  let .const declName _ := e.getAppFn | return .rfl
  unless declNames.contains declName do return .rfl
  let env ← getEnv
  unless hasSmartUnfoldingDecl env declName do
    let some value := env.find? declName |>.bind (·.value?) | return .rfl
    if value.getNumHeadLambdas > e.getAppNumArgs then return .rfl
  let some e' ← unfoldDefinition? e (ignoreTransparency := true) | return .rfl
  return .step (← shareCommon e')

end Lean.Meta.Sym.DSimp
