/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.ForEachExprWhere
import Lean.Compiler.LCNF.CompilerM

namespace Lean.Compiler.LCNF
namespace Closure

/-!
# Dependency collector for code specialization and lambda lifting.

During code specialization and lambda lifting, we have code `C` containing free variables. These free variables
are in a scope, and we say we are computing `C`'s closure.
This module is used to compute the closure.
-/

structure Context where
  /--
  `inScope x` returns `true` if `x` is a variable that is not in `C`.
  -/
  inScope : FVarId → Bool
  /--
  If `abstract x` returns `true`, we convert `x` into a closure parameter. Otherwise,
  we collect the dependencies in the `let`/`fun`-declaration too, and include the declaration in the closure.
  Remark: the lambda lifting pass abstracts all `let`/`fun`-declarations.
  -/
  abstract : FVarId → Bool

/--
State for the `ClosureM` monad.
-/
structure State where
  /--
  Set of already visited free variables.
  -/
  visited : FVarIdSet := {}
  /--
  Free variables that must become new parameters of the code being specialized.
  -/
  params  : Array Param := #[]
  /--
  Let-declarations and local function declarations that are going to be "copied" to the code
  being processed. For example, when this module is used in the code specializer, the let-declarations
  often contain the instance values. In the current specialization heuristic all let-declarations are ground values
  (i.e., they do not contain free-variables).
  However, local function declarations may contain free variables.

  All customers of this module try to avoid work duplication. If a let-declaration is a ground value,
  it most likely will be computed during compilation time, and work duplication is not an issue.
  -/
  decls   : Array CodeDecl := #[]

/--
Monad for implementing the dependency collector.
-/
abbrev ClosureM := ReaderT Context $ StateRefT State CompilerM

/--
Mark a free variable as already visited.
We perform a topological sort over the dependencies.
-/
def markVisited (fvarId : FVarId) : ClosureM Unit :=
  modify fun s => { s with visited := s.visited.insert fvarId }

mutual
 /--
  Collect dependencies in parameters. We need this because parameters may
  contain other type parameters.
  -/
  partial def collectParams (params : Array Param) : ClosureM Unit :=
    params.forM (collectType ·.type)

  partial def collectArg (arg : Arg) : ClosureM Unit :=
    match arg with
    | .erased => return ()
    | .type e => collectType e
    | .fvar fvarId => collectFVar fvarId

  partial def collectLetValue (e : LetValue) : ClosureM Unit := do
    match e with
    | .erased | .value .. => return ()
    | .proj _ _ fvarId => collectFVar fvarId
    | .const _ _ args => args.forM collectArg
    | .fvar fvarId args => collectFVar fvarId; args.forM collectArg

  /--
  Collect dependencies in the given code. We need this function to be able
  to collect dependencies in a local function declaration.
  -/
  partial def collectCode (c : Code) : ClosureM Unit := do
    match c with
    | .let decl k => collectType decl.type; collectLetValue decl.value; collectCode k
    | .fun decl k | .jp decl k => collectFunDecl decl; collectCode k
    | .cases c =>
      collectType c.resultType
      collectFVar c.discr
      c.alts.forM fun alt => do
        match alt with
        | .default k => collectCode k
        | .alt _ ps k => collectParams ps; collectCode k
    | .jmp _ args => args.forM collectArg
    | .unreach type => collectType type
    | .return fvarId => collectFVar fvarId

  /-- Collect dependencies of a local function declaration. -/
  partial def collectFunDecl (decl : FunDecl) : ClosureM Unit := do
    collectType decl.type
    collectParams decl.params
    collectCode decl.value

  /--
  Process the given free variable.
  If it has not already been visited and is in scope, we collect its dependencies.
  -/
  partial def collectFVar (fvarId : FVarId) : ClosureM Unit := do
    unless (← get).visited.contains fvarId do
      markVisited fvarId
      if (← read).inScope fvarId then
        /- We only collect the variables in the scope of the function application being specialized. -/
        if let some funDecl ← findFunDecl? fvarId then
          if (← read).abstract funDecl.fvarId then
            modify fun s => { s with params := s.params.push <| { funDecl with borrow := false } }
          else
            collectFunDecl funDecl
            modify fun s => { s with decls := s.decls.push <| .fun funDecl }
        else if let some param ← findParam? fvarId then
          collectType param.type
          modify fun s => { s with params := s.params.push param }
        else if let some letDecl ← findLetDecl? fvarId then
          collectType letDecl.type
          if (← read).abstract letDecl.fvarId then
            modify fun s => { s with params := s.params.push <| { letDecl with borrow := false } }
          else
            collectLetValue letDecl.value
            modify fun s => { s with decls := s.decls.push <| .let letDecl }
        else
          unreachable!

  /-- Collect dependencies of the given expression. -/
  partial def collectType (type : Expr) : ClosureM Unit := do
    type.forEachWhere Expr.isFVar fun e => collectFVar e.fvarId!

end

def run (x : ClosureM α) (inScope : FVarId → Bool) (abstract : FVarId → Bool := fun _ => true) : CompilerM (α × Array Param × Array CodeDecl) := do
  let (a, s) ← x { inScope, abstract } |>.run {}
  return (a, s.params, s.decls)

end Closure

end Lean.Compiler.LCNF