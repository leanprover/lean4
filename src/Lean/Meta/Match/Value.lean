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
Returns a normal form of the match value `e`, such that two match values denote the same value iff
their normal forms are structurally equal. Distinct `Float`/`Float32` literals can denote the same
value (e.g. `5` and `5.0`), so these are normalized to their bit patterns, consistent with their
`DecidableEq` instances. Other values are returned unchanged.
-/
def normMatchValue (e : Expr) : MetaM Expr := do
  if let some x ← getFloatValue? e then
    return mkApp (mkConst ``Float.ofBits) (mkRawNatLit x.toBits.toNat)
  if let some x ← getFloat32Value? e then
    return mkApp (mkConst ``Float32.ofBits) (mkRawNatLit x.toBits.toNat)
  return e

end Lean.Meta
