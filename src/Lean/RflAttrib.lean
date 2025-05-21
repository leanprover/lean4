/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
prelude

import Lean.PrettyPrinter

namespace Lean
open Meta

def validateRflAttr (declName : Name) : AttrM Unit := do
  let info ← getConstVal declName
  MetaM.run' do
    withOptions (smartUnfolding.set · false) <| withTransparency .all do
      forallTelescopeReducing info.type fun _ type => do
        -- NB: The warning wording should work both for explicit uses of `@[rfl]` as well as the implicit `:= rfl`.
        let some (_, lhs, rhs) := type.eq? |
          throwError m!"not a `rfl`-theorem: the conculsion should be an equality, but is{inlineExpr type}"
        if !(← withOptions (smartUnfolding.set · false) <| withTransparency .all <| isDefEq lhs rhs) then
          let explanation := MessageData.ofLazyM (es := #[lhs, rhs]) do
            let (lhs, rhs) ← addPPExplicitToExposeDiff lhs rhs
            return m!"not a `rfl`-theorem: the left-hand side{indentExpr lhs}\nis not definitionally equal to the right-hand side{indentExpr rhs}"
          throwError explanation

builtin_initialize rflAttr : TagAttribute ←
  registerTagAttribute `rfl "mark theorem as a `rfl`-theorem, to be used by `dsimp`"
    (validate := validateRflAttr) (applicationTime := .afterTypeChecking)
    (asyncMode := .async)

private partial def isRflProofCore (type : Expr) (proof : Expr) : CoreM Bool := do
  match type with
  | .forallE _ _ type _ =>
    if let .lam _ _ proof _ := proof then
      isRflProofCore type proof
    else
      return false
  | _ =>
    if type.isAppOfArity ``Eq 3 then
      if proof.isAppOfArity ``Eq.refl 2 || proof.isAppOfArity ``rfl 2 then
        return true
      else if proof.isAppOfArity ``Eq.symm 4 then
        -- `Eq.symm` of rfl theorem is a rfl theorem
        isRflProofCore type proof.appArg! -- small hack: we don't need to set the exact type
      else if proof.getAppFn.isConst then
        -- The application of a `rfl` theorem is a `rfl` theorem
        -- A constant which is a `rfl` theorem is a `rfl` theorem
        return rflAttr.hasTag (← getEnv) proof.getAppFn.constName!
      else
        return false
    else
      return false

/--
For automatically generated theorems (equational theorems etc.), we want to set the `rfl` attribute
if the proof is `Eq.rfl`, essentially reproducing the behavior before the introduction of the `rfl`
attribute. This function infers the `rfl` attribute based on the declaration value.
-/
def inferRflAttr (declName : Name) : MetaM Unit := do
  let info ← getConstInfo declName
  let isRfl ←
    if let some value := info.value? then
      isRflProofCore info.type value
    else
      pure false
  if isRfl then
    validateRflAttr declName -- just a sanity-check
    rflAttr.setTag declName
