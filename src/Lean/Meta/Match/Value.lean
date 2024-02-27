/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.LitValues
import Lean.Expr

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
  return false

end Lean.Meta
