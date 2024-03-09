/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
prelude
import Lean.PrettyPrinter.Delaborator.Attributes
import Lean.PrettyPrinter.Delaborator.Options
import Lean.Structure

/-!
# Functions for analyzing projections for pretty printing
-/

namespace Lean.PrettyPrinter.Delaborator
open Meta

/--
If this is a structure projection that could delaborate using dot notation,
returns the field name, the number of parameters before the structure argument, and whether this is a parent projection.
Otherwise it fails.
-/
private def projInfo (f : Expr) : MetaM (Name × Nat × Bool) := do
  let .const c@(.str _ field) _ := f.consumeMData | failure
  let field := Name.mkSimple field
  let env ← getEnv
  let some info := env.getProjectionFnInfo? c | failure
  -- Don't use projection notation for instances of classes.
  guard <| !info.fromClass
  let some (.ctorInfo cVal) := env.find? info.ctorName | failure
  let isParentProj := (isSubobjectField? env cVal.induct field).isSome
  return (field, info.numParams, isParentProj)

/--
If this function application could delaborate using generalized field notation,
returns the field name and the index for the argument to be used as the object of the field notation.
Otherwise it fails.
-/
private def generalizedFieldInfo (f : Expr) (args : Array Expr) : MetaM (Name × Nat) := do
  let .const name@(.str _ field) .. := f.consumeMData | failure
  let field := Name.mkSimple field
  let baseName := name.getPrefix
  guard <| !baseName.isAnonymous
  Meta.forallBoundedTelescope (← instantiateMVars <| ← inferType f) args.size fun params _ => do
    for i in [0:params.size] do
      let fvarId := params[i]!.fvarId!
      if (← fvarId.getBinderInfo).isExplicit then
        -- We only consider the first explicit argument, so fail if the parameter does not have the correct type.
        guard <| (← fvarId.getType).cleanupAnnotations.isAppOf baseName
        let argTy ← instantiateMVars <| ← inferType args[i]!
        -- Generalized field notation allows either an an exact match, or a match after `whnfR`.
        if argTy.consumeMData.isAppOf baseName then
          return (field, i)
        else if (← Meta.whnfR argTy).isAppOf baseName then
          return (field, i)
        else
          failure
      else
        -- If not explicit, then make sure that this parameter can't be used for field notation.
        guard <| ! (← fvarId.getType).cleanupAnnotations.isAppOf baseName
    failure

/--
If `f` is a function that can be used for field notation,
returns the field name to use and the argument index for the object of the field notation.
-/
def fieldNotationCandidate? (f : Expr) (args : Array Expr) (useGeneralizedFieldNotation : Bool) : MetaM (Option (Name × Nat)) := do
  let env ← getEnv
  let .const name .. := f.consumeMData | return none
  if name.getPrefix.isAnonymous then return none
  -- If there is `pp_nodot` on this function, then don't use field notation for it.
  if hasPPNoDotAttribute env name then
    return none
  -- Handle structure projections
  try
    let (field, numParams, _) ← projInfo f
    return (field, numParams)
  catch _ => pure ()
  -- Handle generalized field notation
  if useGeneralizedFieldNotation then
    try
      return ← generalizedFieldInfo f args
    catch _ => pure ()
  -- It's not handled by any of the above.
  return none

/--
Returns `true` if `e` is an application that is a projection to a parent structure.
If `explicit` is `true`, then further requires that the structure have no parameters.
-/
def isParentProj (explicit : Bool) (e : Expr) : MetaM Bool := do
  unless e.isApp do return false
  try
    let (_, numParams, isParentProj) ← projInfo e.getAppFn
    return isParentProj && (!explicit || numParams == 0) && e.getAppNumArgs == numParams + 1
  catch _ =>
    return false
