/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.AppBuilder
import Lean.PrettyPrinter
namespace Lean.Elab
open Meta

private structure InhabitantCache (useOfNonempty : Bool) where
  /-- Map from types to inhabitants. -/
  inhabitants : ExprMap Expr := {}
  /-- Local instances to eliminate with `mkLetFVars`. -/
  localInstances : Array Expr := #[]
  /-- Worklist of expressions to try to get more inhabitants out of.
  The types of these are functions `α → β`, and in `resolve` we try to inhabit `α`. -/
  unresolved : Array Expr := #[]

private def InhabitantCache.withInhabitant (cache : InhabitantCache useOfNonempty) (x : Expr)
    (k : InhabitantCache useOfNonempty → MetaM α) : MetaM α := do
  let xTy ← whnfCore (← inferType x)
  if cache.inhabitants.contains xTy then
    k cache
  else
    -- Add `Inhabited` instance to help find inhabitants through typeclass inference later.
    let u ← getLevel xTy
    let instTy := mkApp (.const ``Inhabited [u]) xTy
    let instVal := mkApp2 (.const ``Inhabited.mk [u]) xTy x
    withLetDecl `inst instTy instVal fun inst =>
      k { inhabitants := cache.inhabitants.insert xTy x
          localInstances := cache.localInstances.push inst
          unresolved := if xTy.isForall then cache.unresolved.push x else cache.unresolved }

private def InhabitantCache.withInhabitants (cache : InhabitantCache useOfNonempty) (xs : Array Expr)
    (k : InhabitantCache useOfNonempty → MetaM α) : MetaM α := do
  let rec go (i : Nat) cache : MetaM α := do
    if h : i < xs.size then
      cache.withInhabitant xs[i] (go (i + 1))
    else
      k cache
  go 0 cache

/-- Constructs an inhabitant if possible.
Eliminates the `localInstances` let variables introduced by `withInhabitant`. -/
private def InhabitantCache.mkInhabitant? (cache : InhabitantCache useOfNonempty) (type : Expr) :
    MetaM (Option Expr) := do
  if let some x := cache.inhabitants[type]? then
    return some x
  else
    try
      let x ← if useOfNonempty then mkOfNonempty type else mkDefault type
      mkLetFVars (usedLetOnly := true) cache.localInstances x
    catch _ =>
      return none

/-- Tries to find new inhabitants from the worklist. Does a single pass, instantiating foralls as far as possible. -/
private def InhabitantCache.resolve (cache : InhabitantCache useOfNonempty)
    (kOk : InhabitantCache useOfNonempty → MetaM α) (kFail : MetaM α) : MetaM α := do
  let unresolved := cache.unresolved
  let rec go (i : Nat) (cache : InhabitantCache useOfNonempty) (doOk : Bool) : MetaM α := do
    if h : i < unresolved.size then
      let mut x := unresolved[i]
      let mut xTy ← whnfCore (← inferType x)
      let mut changed := false
      while xTy.isForall do
        if let some domVal ← cache.mkInhabitant? xTy.bindingDomain! then
          x := .app x domVal
          xTy ← whnfCore (xTy.bindingBody!.instantiate1 domVal)
          changed := true
        else
          break
      if changed then
        cache.withInhabitant x fun cache => do go (i + 1) cache true
      else
        go (i + 1) { cache with unresolved := cache.unresolved.push x } doOk
    else
      if doOk then
        kOk cache
      else
        kFail
  go 0 { cache with unresolved := #[] } false

/--
Find an inhabitant while doing delta unfolding.
-/
private partial def mkInhabitantForAux? (useOfNonempty : Bool) (cache : InhabitantCache useOfNonempty) (type : Expr) :
    MetaM (Option Expr) := withIncRecDepth do
  let type ← whnfCore type
  if type.isForall then
    forallTelescope type fun xs type' =>
      cache.withInhabitants xs fun cache => do
        let some val ← mkInhabitantForAux? _ cache type' | return none
        mkLambdaFVars xs val
  else if let some val ← cache.mkInhabitant? type then
    return val
  else
    cache.resolve
      (kOk := fun cache => mkInhabitantForAux? _ cache type)
      (kFail := do
        if let some type ← unfoldDefinition? type then
          mkInhabitantForAux? _ cache type
        else
          return none)

/- TODO: add a global IO.Ref to let users customize/extend this procedure -/
def mkInhabitantFor (declName : Name) (type : Expr) : MetaM Expr := do
  if let some val ← mkInhabitantForAux? false {} type <||> mkInhabitantForAux? true {} type then
    return val
  else
    throwError "\
      failed to compile 'partial' definition '{declName}', could not prove that the type\
      {indentExpr type}\n\
      is nonempty.\n\
      \n\
      This process uses multiple strategies:\n\
      - It looks for a parameter that matches the return type.\n\
      - It tries synthesizing '{.ofConstName ``Inhabited}' and '{.ofConstName ``Nonempty}' \
        instances for the return type, while making every parameter into a local '{.ofConstName ``Inhabited}' instance.\n\
      - It tries unfolding the return type.\n\
      \n\
      If the return type is defined using the 'structure' or 'inductive' command, \
      you can try adding a 'deriving Nonempty' clause to it."

end Lean.Elab
