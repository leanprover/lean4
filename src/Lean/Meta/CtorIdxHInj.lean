/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module
prelude
public import Lean.Meta.Basic
import Lean.Meta.Tactic.Refl
import Lean.Meta.Tactic.Cases
import Lean.Meta.Tactic.Assumption
import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.SameCtorUtils
import Lean.Meta.Constructions.CtorIdx
import Lean.ReservedRealizableThm
namespace Lean.Meta

partial def repeatIntroSubstRefl (mvarId : MVarId) : MetaM Unit := do
  let type ← mvarId.getType
  if type.isForall then
    let (h, mvarId) ← mvarId.intro1
    let (h, mvarId) ← heqToEq mvarId h
    let (_, mvarId) ← substEq mvarId h
    repeatIntroSubstRefl mvarId
  else
    mvarId.refl


def ctorIdxHInj : RealizableTheoremSpec where
  suffixBase := "hinj"
  shouldExist := fun env declName _ =>
    (isCtorIdxCore? env declName).isSome
  generate := fun declName _ _ kType kProof => do
    let some indVal ← isCtorIdx? declName
      | throwError "Not a ctorIdx: {declName}"
    let us := indVal.levelParams.map mkLevelParam
    let thmType ←
      forallBoundedTelescope indVal.type (indVal.numParams + indVal.numIndices) fun xs1 _ => do
      forallBoundedTelescope indVal.type (indVal.numParams + indVal.numIndices) fun xs2 _ => do
      withImplicitBinderInfos xs1 do
      withImplicitBinderInfos xs2 do
      withPrimedNames xs2 do
      withLocalDeclD `x  (mkAppN (mkConst indVal.name us) xs1) fun x1 => do
      withLocalDeclD `x' (mkAppN (mkConst indVal.name us) xs2) fun x2 => do
        let ctorIdxApp1 := mkAppN (mkConst (mkCtorIdxName indVal.name) us) (xs1.push x1)
        let ctorIdxApp2 := mkAppN (mkConst (mkCtorIdxName indVal.name) us) (xs2.push x2)
        let mut thmType ← mkEq ctorIdxApp1 ctorIdxApp2
        for a1 in (xs1.push x1).reverse, a2 in (xs2.push x2).reverse do
          if (← isProof a1) then
            continue
          let name := (← a1.fvarId!.getUserName).appendAfter "_eq"
          let eq ← mkEqHEq a1 a2
          thmType := mkForall name .default eq thmType
        mkForallFVars (xs1.push x1 ++ xs2.push x2) thmType
    kType indVal.levelParams thmType

    let thmVal ← mkFreshExprSyntheticOpaqueMVar thmType
    let mut mvarId := thmVal.mvarId!
    mvarId := (← mvarId.introN (2 * (indVal.numParams + indVal.numIndices + 1))).2
    repeatIntroSubstRefl mvarId
    let thmVal ← instantiateMVars thmVal
    kProof thmVal

builtin_initialize ctorIdxHInj.register

public def mkCtorIdxHInjThmFor (ctorIdxName : Name) : MetaM Name :=
  ctorIdxHInj.gen ctorIdxName

end Lean.Meta
