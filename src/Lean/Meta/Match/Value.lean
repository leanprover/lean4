/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.LitValues

public section

namespace Lean.Meta

/-- Return true is `e` is a term that should be processed by the `match`-compiler using `casesValues` -/
def isMatchValue (e : Expr) : MetaM Bool := do
  let e ← instantiateMVars e
  if (← getNatValue? e).isSome then return true
  if (← getIntValue? e).isSome then return true
  if (← getFinValue? e).isSome then return true
  if (← getBitVecValue? e).isSome then return true
  if (getStringValue? e).isSome then return true
  if (← getCharValue? e).isSome then return true
  if (← getUInt8Value? e).isSome then return true
  if (← getUInt16Value? e).isSome then return true
  if (← getUInt32Value? e).isSome then return true
  if (← getUInt64Value? e).isSome then return true
  if (← getFloatValue? e).isSome then return true
  if (← getFloat32Value? e).isSome then return true
  return false

/--
Returns `true` if the match values `a` and `b` denote the same value. Distinct `Float`/`Float32`
literals can denote the same value (e.g. `5` and `5.0`), so these are compared by bit pattern,
consistent with their `DecidableEq` instances.
-/
def matchValuesEq (a b : Expr) : MetaM Bool := do
  if a == b then return true
  if let some x ← getFloatValue? a then
    if let some y ← getFloatValue? b then return x.toBits == y.toBits
  if let some x ← getFloat32Value? a then
    if let some y ← getFloat32Value? b then return x.toBits == y.toBits
  return false

end Lean.Meta
