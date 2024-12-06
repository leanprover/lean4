/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.LitValues
import Lean.Meta.Offset

namespace Lean.Meta

private def getConstructorVal? (env : Environment) (ctorName : Name) : Option ConstructorVal :=
  match env.find? ctorName with
  | some (.ctorInfo v) => v
  | _                  => none

/--
If `e` is a constructor application,
then return the corresponding `ConstructorVal`.
-/
def isConstructorAppCore? (e : Expr) : MetaM (Option ConstructorVal) := do
  let .const n _ := e.getAppFn | return none
  let some v := getConstructorVal? (← getEnv) n | return none
  if v.numParams + v.numFields == e.getAppNumArgs then
    return some v
  else
    return none

/--
If `e` is a constructor application or a builtin literal defeq to a constructor application,
then return the corresponding `ConstructorVal`.
-/
def isConstructorApp? (e : Expr) : MetaM (Option ConstructorVal) := do
  isConstructorAppCore? (← litToCtor e)

/--
Similar to `isConstructorApp?`, but uses `whnf`.
It also uses `isOffset?` for `Nat`.

See also `Lean.Meta.constructorApp'?`.
-/
def isConstructorApp'? (e : Expr) : MetaM (Option ConstructorVal) := do
  if let some (_, k) ← isOffset? e then
    if k = 0 then
      return none
    else
      let .ctorInfo val ← getConstInfo ``Nat.succ | return none
      return some val
  else if let some r ← isConstructorApp? e then
    return r
  else try
    /-
    We added the `try` block here because `whnf` fails at terms `n ^ m`
    when `m` is a big numeral, and `n` is a numeral. This is a little bit hackish.
    -/
    isConstructorApp? (← whnf e)
  catch _ =>
    return none

/--
Returns `true`, if `e` is constructor application of builtin literal defeq to
a constructor application.
-/
def isConstructorApp (e : Expr) : MetaM Bool :=
  return (← isConstructorApp? e).isSome

/--
Returns `true` if `isConstructorApp e` or `isConstructorApp (← whnf e)`
-/
def isConstructorApp' (e : Expr) : MetaM Bool := do
  if (← isConstructorApp e) then return true
  return (← isConstructorApp (← whnf e))

/--
If `e` is a constructor application, return a pair containing the corresponding `ConstructorVal` and the constructor
application arguments.
-/
def constructorApp? (e : Expr) : MetaM (Option (ConstructorVal × Array Expr)) := do
  let e ← litToCtor e
  let .const declName _ := e.getAppFn | return none
  let some v := getConstructorVal? (← getEnv) declName | return none
  if v.numParams + v.numFields == e.getAppNumArgs then
    return some (v, e.getAppArgs)
  else
    return none

/--
Similar to `constructorApp?`, but on failure it puts `e` in WHNF and tries again.
It also uses `isOffset?` for `Nat`.

See also `Lean.Meta.isConstructorApp'?`.
-/
def constructorApp'? (e : Expr) : MetaM (Option (ConstructorVal × Array Expr)) := do
  if let some (e, k) ← isOffset? e then
    if k = 0 then
      return none
    else
      let .ctorInfo val ← getConstInfo ``Nat.succ | return none
      if k = 1 then return some (val, #[e])
      else return some (val, #[mkNatAdd e (toExpr (k-1))])
  else if let some r ← constructorApp? e then
    return some r
  else try
    /-
    We added the `try` block here because `whnf` fails at terms `n ^ m`
    when `m` is a big numeral, and `n` is a numeral. This is a little bit hackish.
    -/
    constructorApp? (← whnf e)
  catch _ =>
    return none

end Lean.Meta
