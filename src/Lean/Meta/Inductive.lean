/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Parth Shastri
-/
prelude
import Lean.Meta.Basic

/-! # Helper methods for inductive datatypes -/

namespace Lean.Meta

/-- Return true if the types of the given constructors are compatible. -/
def compatibleCtors (ctorName₁ ctorName₂ : Name) : MetaM Bool := do
  let ctorInfo₁ ← getConstInfoCtor ctorName₁
  let ctorInfo₂ ← getConstInfoCtor ctorName₂
  if ctorInfo₁.induct != ctorInfo₂.induct then
    return false
  else
    let (_, _, ctorType₁) ← forallMetaTelescope ctorInfo₁.type
    let (_, _, ctorType₂) ← forallMetaTelescope ctorInfo₂.type
    isDefEq ctorType₁ ctorType₂

/--
  An inductive type is called reflexive if it has at least one constructor that takes as an argument a function returning an
  inductive type (possibly the same type being defined) in the same mutual declaration.
  Consider the type:
  ```
  inductive WideTree where
    | branch : (Nat -> WideTree) -> WideTree
    | leaf : WideTree
  ```
  this is reflexive due to the presence of the `branch : (Nat -> WideTree) -> WideTree` constructor.
  See also: 'Inductive Definitions in the system Coq Rules and Properties' by Christine Paulin-Mohring
  Section 2.2, Definition 3

  To correctly handle nested inductives, we determine whether an inductive type is reflexive by checking the type of its
  recursor. The recursor for a reflexive inductive type will have at least one minor premise (i.e. case) with a forall
  quantified induction hypothesis, so we search for such a minor premise.
-/
def isReflexiveInductive (indName : Name) : MetaM Bool := do
  let recVal ← getConstInfoRec (mkRecName indName)
  forallTelescope recVal.type fun args _ => do
  let motives := args[recVal.numParams:recVal.numParams + recVal.numMotives]
  for idx in [:recVal.numMinors] do
    let minor ← args[recVal.numParams + recVal.numMotives + idx]!.fvarId!.getType
    let isMinorReflexive ← forallTelescope minor fun minorArgs _ => do
      for arg in minorArgs do
        let argTy ← arg.fvarId!.getType
        unless argTy.isForall do
          continue
        let argFn := argTy.getForallBody.getAppFn
        if motives.any (· == argFn) then
          return true
      return false
    if isMinorReflexive then
      return true
  return false

end Lean.Meta
