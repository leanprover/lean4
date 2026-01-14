/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Meta.Basic
import Lean.Meta.Check
import Lean.Meta.WHNF

public section

namespace Lean
open Meta

/--
There are defeq theorems that only hold at transparency `.all`, but also others that hold
(from the kernel's point of view) but where the defeq checker here will run out of cycles.

So we try the more careful first.
-/
private def isDefEqCareful (e1 e2 : Expr) : MetaM Bool := do
  withOptions (smartUnfolding.set · false) <| do
    withDefault (isDefEq e1 e2) <||> withTransparency .all (isDefEq e1 e2)

def validateDefEqAttr (declName : Name) : AttrM Unit := do
  let info ← getConstVal declName
  MetaM.run' do
    withTransparency .all do -- we want to look through defs in `info.type` all the way to `Eq`
      forallTelescopeReducing info.type fun _ type => do
        let type ← whnf type
        -- NB: The warning wording should work both for explicit uses of `@[defeq]` as well as the implicit `:= rfl`.
        let some (_, lhs, rhs) := type.eq? |
          throwError m!"Not a definitional equality: the conclusion should be an equality, but is{inlineExpr type}"
        let ok ← isDefEqCareful lhs rhs
        unless ok do
          let explanation := MessageData.ofLazyM (es := #[lhs, rhs]) do
            let (lhs, rhs) ← addPPExplicitToExposeDiff lhs rhs
            let mut msg := m!"Not a definitional equality: the left-hand side{indentExpr lhs}\nis \
              not definitionally equal to the right-hand side{indentExpr rhs}"
            if (← getEnv).isExporting then
              let okPrivately ← withoutExporting <| isDefEqCareful lhs rhs
              if okPrivately then
                msg := msg ++ .note m!"This theorem is exported from the current module. \
                  This requires that all definitions that need to be unfolded to prove this \
                  theorem must be exposed."
            pure msg
          throwError explanation

/--
Marks the theorem as a definitional equality.

The theorem must be an equality that holds by `rfl`. This allows `dsimp` to use this theorem
when rewriting.

A theorem with with a definition that is (syntactically) `:= rfl` is implicitly marked `@[defeq]`.
To avoid this behavior, write `:= (rfl)` instead.

The attribute should be given before a `@[simp]` attribute to have effect.

When using the module system, an exported theorem can only be `@[defeq]` if all definitions that
need to be unfolded to prove the theorem are exported and exposed.
-/
@[builtin_doc]
builtin_initialize defeqAttr : TagAttribute ←
  registerTagAttribute `defeq "mark theorem as a definitional equality, to be used by `dsimp`"
    (validate := validateDefEqAttr) (applicationTime := .afterTypeChecking)
    (asyncMode := .async .mainEnv)

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
  withoutExporting do
    let info ← getConstInfo declName
    let isRfl ←
      if let some value := info.value? then
        isRflProofCore info.type value
      else
        pure false
    if isRfl then
      try
        withExporting (isExporting := !isPrivateName declName) do
          validateDefEqAttr declName -- sanity-check: would we have accepted `@[defeq]` on this?
      catch e =>
        logError m!"Theorem {declName} has a `rfl`-proof and was thus inferred to be `@[defeq]`, \
          but validating that attribute failed:{indentD e.toMessageData}"
      defeqAttr.setTag declName
