/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
prelude

import Lean.PrettyPrinter

namespace Lean
open Meta

def validateDefEqAttr (declName : Name) : AttrM Unit := do
  let info ← getConstVal declName
  MetaM.run' do
    withTransparency .all do
      forallTelescopeReducing info.type fun _ type => do
        let type ← whnf type
        -- NB: The warning wording should work both for explicit uses of `@[defeq]` as well as the implicit `:= rfl`.
        let some (_, lhs, rhs) := type.eq? |
          throwError m!"Not a definitional equality: the conclusion should be an equality, but is{inlineExpr type}"
        let ok ← withOptions (smartUnfolding.set · false) <| isDefEq lhs rhs
        unless ok do
          let explanation := MessageData.ofLazyM (es := #[lhs, rhs]) do
            let (lhs, rhs) ← addPPExplicitToExposeDiff lhs rhs
            let mut msg := m!"Not a definitional equality: the left-hand side{indentExpr lhs}\nis \
              not definitionally equal to the right-hand side{indentExpr rhs}"
            if (← getEnv).isExporting then
              let okPrivately ← withoutExporting <| withOptions (smartUnfolding.set · false) <| isDefEq lhs rhs
              if okPrivately then
                msg := msg ++ .note m!"This theorem is exported from the current module. \
                  This requires that all definitions that need to be unfolded to prove this \
                  theorem must be exposed."
            pure msg
          throwError explanation

/--
Markes the theorem as a definitional equality.

The theorem must be an equality that holds by `rfl`. This allows `dsimp` to use this theorem
when rewriting.

A theorem with a body is written exactly as `:= rfl` is implicitly marked `@[defeq]`. To avoid
this behavior, write `:= (rfl)` instead.

The attribute should be given before a `@[simp]` attribute to have effect.

When using the module system, an exported theorem can only be `@[defeq]` if all definitions that
need to be unfolded to prove the theorem are also exported.
-/
@[builtin_doc]
builtin_initialize defeqAttr : TagAttribute ←
  registerTagAttribute `defeq "mark theorem as a definitional equality, to be used by `dsimp`"
    (validate := validateDefEqAttr) (applicationTime := .afterTypeChecking)
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
        -- `Eq.symm` of rfl proof is a rfl proof
        isRflProofCore type proof.appArg! -- small hack: we don't need to set the exact type
      else if proof.getAppFn.isConst then
        -- The application of a `defeq` theorem is a `rfl` proof
        return defeqAttr.hasTag (← getEnv) proof.getAppFn.constName!
      else
        return false
    else
      return false

/--
For automatically generated theorems (equational theorems etc.), we want to set the `defeq` attribute
if the proof is `rfl`, essentially reproducing the behavior before the introduction of the `defeq`
attribute. This function infers the `defeq` attribute based on the declaration value.
-/
def inferDefEqAttr (declName : Name) : MetaM Unit := do
  let info ← getConstInfo declName
  let isRfl ←
    if let some value := info.value? then
      isRflProofCore info.type value
    else
      pure false
  if isRfl then
    -- TODO: We could run `validateDefEqAttr` here as a sanity check, once
    -- equational lemmas are exported iff their definition's bodies are exposed.
    -- validateDefEqAttr declName -- just a sanity-check
    defeqAttr.setTag declName
