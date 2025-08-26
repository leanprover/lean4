/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

prelude
public import Lean.Meta.InferType
public import Lean.Meta.WHNF
public import Lean.PrettyPrinter.Delaborator.Attributes
public import Lean.PrettyPrinter.Delaborator.Options
public import Lean.Structure

public section

/-!
# Functions for analyzing projections for pretty printing
-/

namespace Lean.PrettyPrinter.Delaborator
open Meta

/--
If this constant is a structure projection that could delaborate using dot notation, returns
- the field name,
- the number of parameters before the structure argument,
- whether this is a "true" projection (or else a non-subobject parent projection),
- whether this is a parent projection, and
- whether this is a class projection.
Otherwise it returns `none`.
-/
private def projInfo (c : Name) : MetaM (Option (Name × Nat × Bool × Bool × Bool)) := do
  let env ← getEnv
  let .str s field := c | return none
  let field := Name.mkSimple field
  let some structInfo := getStructureInfo? env s | return none
  let isFromClass := isClass env s
  let info ← getConstInfoInduct s
  if let some fieldInfo := getFieldInfo? env s field then
    return (field, info.numParams, true, fieldInfo.subobject?.isSome, isFromClass)
  else if structInfo.parentInfo.any (·.projFn == c) then
    return (field, info.numParams, false, true, isFromClass)
  else
    return none

/--
Checks that `e` is an application of a constant that equals `baseName`, taking into consideration private name mangling.
-/
private def isAppOfBaseName (env : Environment) (e : Expr) (baseName : Name) : Bool :=
  if let some c := e.cleanupAnnotations.getAppFn.constName? then
    privateToUserName c == baseName && !isInaccessiblePrivateName env c
  else
    false

/--
Like `Lean.Elab.Term.typeMatchesBaseName` but does not use `Function` for pi types.
-/
private partial def typeMatchesBaseName (type : Expr) (baseName : Name) : MetaM Bool := do
  withReducibleAndInstances do
    if isAppOfBaseName (← getEnv) type baseName then
      return true
    else
      let type ← whnfCore type
      if isAppOfBaseName (← getEnv) type baseName then
        return true
      else
        match ← unfoldDefinition? type with
        | some type' => typeMatchesBaseName type' baseName
        | none => return false

/--
If this constant application could delaborate using generalized field notation with little confusion,
returns the field name and the index for the argument to be used as the object of the field notation.
Otherwise it fails.
-/
private def generalizedFieldInfo (c : Name) (args : Array Expr) : MetaM (Name × Nat) := do
  let .str baseName field := c | failure
  let baseName := privateToUserName baseName
  guard <| !baseName.isAnonymous
  let field := Name.mkSimple field
  -- Disallow `Function` since it is used for pi types.
  guard <| baseName != `Function
  let info ← getConstInfo c
  -- Search for the first argument that could be used for field notation
  -- and make sure it is the first explicit argument.
  forallBoundedTelescope info.type args.size fun params _ => do
    for h : i in *...params.size do
      let fvarId := params[i].fvarId!
      -- If there is a motive, we will treat this as a sort of control flow structure and so we won't use field notation.
      -- Plus, recursors tend to be riskier when using dot notation.
      if (← fvarId.getUserName) == `motive then
        failure
      if (← typeMatchesBaseName (← fvarId.getType) baseName) then
        guard (← fvarId.getBinderInfo).isExplicit
        -- We require an exact match for the base name.
        -- While `Lean.Elab.Term.resolveLValLoop` is able to unfold the type and iterate, we do not attempt to exploit this feature.
        -- (To get it right, we would need to check that each relevant namespace does not contain a declaration named `field`.)
        guard <| isAppOfBaseName (← getEnv) (← instantiateMVars <| ← inferType args[i]!) baseName
        return (field, i)
      else
        -- We only use the first explicit argument for field notation.
        guard !(← fvarId.getBinderInfo).isExplicit
    failure

private def testAppOf (e : Expr) (c : Name) : MetaM Bool := do
  if e.isAppOf c then
    return true
  else
    return (← whnfD e).isAppOf c

/--
If `f` is a function that can be used for field notation,
returns the field name to use and the argument index for the object of the field notation.
-/
def fieldNotationCandidate? (f : Expr) (args : Array Expr) (useGeneralizedFieldNotation : Bool) : MetaM (Option (Name × Nat)) := do
  let env ← getEnv
  let .const c .. := f.consumeMData | return none
  if isInaccessiblePrivateName (← getEnv) c then
    return none
  if c.getPrefix.isAnonymous then return none
  -- If there is `pp_nodot` on this function, then don't use field notation for it.
  if hasPPNoDotAttribute env c then
    return none
  -- Handle structure projections
  if let some (field, numParams, _isTrueProj, isParentProj, isFromClass) ← projInfo c then
    -- Don't use field notation for classes, unless it is a parent projection.
    unless !isFromClass || isParentProj do return none
    unless numParams < args.size do return none
    unless ← testAppOf (← inferType args[numParams]!) c.getPrefix do return none
    return (field, numParams)
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
  let .const c .. := e.getAppFn | return none
  let some (field, numParams, isTrueProj, isParentProj, _isFromClass) ← projInfo c | return none
  if isTrueProj && isParentProj && (!explicit || numParams == 0) && e.getAppNumArgs == numParams + 1 then
    return some field
  else
    return none

/--
Returns `true` if `e` is an application that is a projection to a parent structure.
If `explicit` is `true`, then requires that the structure have no parameters.
-/
def isParentProj (explicit : Bool) (e : Expr) : MetaM Bool := do
  return (← parentProj? explicit e).isSome
