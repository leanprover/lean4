/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
prelude
import Lean.Meta.InferType
import Lean.PrettyPrinter.Delaborator.Attributes
import Lean.PrettyPrinter.Delaborator.Options
import Lean.Structure

/-!
# Functions for analyzing projections for pretty printing
-/

namespace Lean.PrettyPrinter.Delaborator
open Meta

/--
If this constant is a structure projection that could delaborate using dot notation,
returns the field name, the number of parameters before the structure argument, and whether this is a parent projection.
Otherwise it fails.
-/
private def projInfo (c : Name) : MetaM (Name × Nat × Bool) := do
  let .str _ field := c | failure
  let field := Name.mkSimple field
  let env ← getEnv
  let some info := env.getProjectionFnInfo? c | failure
  -- Don't use projection notation for instances of classes.
  guard <| !info.fromClass
  let some (.ctorInfo cVal) := env.find? info.ctorName | failure
  let isParentProj := (isSubobjectField? env cVal.induct field).isSome
  return (field, info.numParams, isParentProj)

/--
Like `Lean.Elab.Term.typeMatchesBaseName` but does not use `Function` for pi types.
-/
private def typeMatchesBaseName (type : Expr) (baseName : Name) : MetaM Bool := do
  if type.cleanupAnnotations.isAppOf baseName then
    return true
  else
    return (← whnfR type).isAppOf baseName

/--
If this constant application could delaborate using generalized field notation with little confusion,
returns the field name and the index for the argument to be used as the object of the field notation.
Otherwise it fails.
-/
private def generalizedFieldInfo (c : Name) (args : Array Expr) : MetaM (Name × Nat) := do
  let .str _ field := c | failure
  let field := Name.mkSimple field
  let baseName := c.getPrefix
  guard <| !baseName.isAnonymous
  -- Disallow `Function` since it is used for pi types.
  guard <| baseName != `Function
  let info ← getConstInfo c
  -- Search for the first argument that could be used for field notation
  -- and make sure it is the first explicit argument.
  forallBoundedTelescope info.type args.size fun params _ => do
    for i in [0:params.size] do
      let fvarId := params[i]!.fvarId!
      -- If there is a motive, we will treat this as a sort of control flow structure and so we won't use field notation.
      -- Plus, recursors tend to be riskier when using dot notation.
      if (← fvarId.getUserName) == `motive then
        failure
      if (← typeMatchesBaseName (← fvarId.getType) baseName) then
        guard (← fvarId.getBinderInfo).isExplicit
        -- We require an exact match for the base name.
        -- While `Lean.Elab.Term.resolveLValLoop` is able to unfold the type and iterate, we do not attempt to exploit this feature.
        -- (To get it right, we would need to check that each relevant namespace does not contain a declaration named `field`.)
        guard <| (← instantiateMVars <| ← inferType args[i]!).consumeMData.isAppOf baseName
        return (field, i)
      else
        -- We only use the first explicit argument for field notation.
        guard !(← fvarId.getBinderInfo).isExplicit
    failure

/--
If `f` is a function that can be used for field notation,
returns the field name to use and the argument index for the object of the field notation.
-/
def fieldNotationCandidate? (f : Expr) (args : Array Expr) (useGeneralizedFieldNotation : Bool) : MetaM (Option (Name × Nat)) := do
  let env ← getEnv
  let .const c .. := f.consumeMData | return none
  if c.getPrefix.isAnonymous then return none
  -- If there is `pp_nodot` on this function, then don't use field notation for it.
  if hasPPNoDotAttribute env c then
    return none
  -- Handle structure projections
  try
    let (field, numParams, _) ← projInfo c
    unless numParams + 1 ≤ args.size do return none
    unless (← whnf <| ← inferType args[numParams]!).isAppOf c.getPrefix do return none
    return (field, numParams)
  catch _ => pure ()
  -- Handle generalized field notation
  if useGeneralizedFieldNotation then
    try
      -- Avoid field notation for theorems
      guard !(← isProof f)
      return ← generalizedFieldInfo c args
    catch _ => pure ()
  -- It's not handled by any of the above.
  return none

/--
Returns the field name of the projection if `e` is an application that is a projection to a parent structure.
If `explicit` is `true`, then requires that the structure have no parameters.
-/
def parentProj? (explicit : Bool) (e : Expr) : MetaM (Option Name) := do
  unless e.isApp do return none
  try
    let .const c .. := e.getAppFn | failure
    let (field, numParams, isParentProj) ← projInfo c
    if isParentProj && (!explicit || numParams == 0) && e.getAppNumArgs == numParams + 1 then
      return some field
    else
      return none
  catch _ =>
    return none

/--
Returns `true` if `e` is an application that is a projection to a parent structure.
If `explicit` is `true`, then requires that the structure have no parameters.
-/
def isParentProj (explicit : Bool) (e : Expr) : MetaM Bool := do
  return (← parentProj? explicit e).isSome
