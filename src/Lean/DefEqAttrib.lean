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

register_builtin_option backward.defeqAttrib.useBackward : Bool := {
  defValue := false
  descr    := "When true, `dsimp` also uses theorems tagged `@[backward_defeq]`, i.e. \
    theorems inferred to be rfl only at default (not instance) transparency. Set this \
    locally (e.g. `set_option backward.defeqAttrib.useBackward true in ...`) to restore the \
    pre-stricter-inference behavior for a specific proof."
}

register_builtin_option backward.inferDefEqOnRfl : Bool := {
  defValue := false
  descr    := "Adaption helper. When true, theorems written `:= rfl` (and that do not \
    already carry a `[defeq]` or `[backward_defeq]` attribute) are inferred to be \
    `[defeq]` (when the equation holds at instance transparency) or `[backward_defeq]` \
    (otherwise). Use this option to opt out of the post-migration default of tagging \
    `:= rfl` theorems with `[backward_defeq]` only, and instead tag with `[defeq]` \
    whenever the strict check passes. Combine with `backward.inferDefEqOnRfl.trace` \
    to log which attribute was inferred."
}

register_builtin_option backward.inferDefEqOnRfl.trace : Bool := {
  defValue := false
  descr    := "When true (and `backward.inferDefEqOnRfl` is also true), emit an info \
    message for each `:= rfl` theorem inferred to be `[defeq]`."
}

/--
There are defeq theorems that only hold at transparency `.all`, but also others that hold
(from the kernel's point of view) but where the defeq checker here will run out of cycles.

So we try the more careful first.
-/
private def isDefEqCareful (e1 e2 : Expr) : MetaM Bool := do
  withOptions (smartUnfolding.set · false) <| do
    withDefault (isDefEq e1 e2) <||> withTransparency .all (isDefEq e1 e2)

private def withEqLhsRhs (type : Expr) (k : Expr → Expr → MetaM α) : MetaM α := do
  withTransparency .all do -- we want to look through defs in `info.type` all the way to `Eq`
    forallTelescopeReducing type fun _ type => do
      let type ← whnf type
      let some (_, lhs, rhs) := type.eq? |
        throwError m!"Not a definitional equality: the conclusion should be an equality, but is{inlineExpr type}"
      k lhs rhs

/--
Validates that `declName` is a definitional equality at `.default`/`.all` transparency
(the legacy permissive check). Throws a diagnostic error if not. This is used as the
validator for the `@[backward_defeq]` attribute.
-/
def validateBackwardDefEqAttr (declName : Name) : AttrM Unit := do
  let info ← getConstVal declName
  MetaM.run' do withEqLhsRhs info.type fun lhs rhs => do
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
Validates that `declName` is a definitional equality at `.instances` transparency
(the strict check matching the transparency used by `dsimp`). Throws a diagnostic
error if not. This is used as the validator for the `@[defeq]` attribute.
-/
def validateDefEqAttr (declName : Name) : AttrM Unit := do
  let info ← getConstVal declName
  MetaM.run' do withEqLhsRhs info.type fun lhs rhs => do
    let ok ← withReducibleAndInstances <| isDefEq lhs rhs
    unless ok do
      let explanation := MessageData.ofLazyM (es := #[lhs, rhs]) do
        let (lhs, rhs) ← addPPExplicitToExposeDiff lhs rhs
        let mut msg := m!"Not a definitional equality at instance transparency: \
          the left-hand side{indentExpr lhs}\nis not definitionally equal to the \
          right-hand side{indentExpr rhs}\nat the transparency used by `dsimp`"
        let okPermissive ← isDefEqCareful lhs rhs
        if okPermissive then
          msg := msg ++ .note m!"The equality holds at default/all transparency. \
            Use `@[backward_defeq]` instead, or rewrite the proof so that the equality \
            holds at instance transparency."
        else if (← getEnv).isExporting then
          let okPrivately ← withoutExporting <| withReducibleAndInstances <| isDefEq lhs rhs
          if okPrivately then
            msg := msg ++ .note m!"This theorem is exported from the current module. \
              This requires that all definitions that need to be unfolded to prove this \
              theorem must be exposed."
        pure msg
      throwError explanation

/--
Marks a theorem as a definitional equality under the permissive transparency rules that
predated the stricter `@[defeq]` inference (i.e. an equality that holds at `.default` or
`.all` transparency, but possibly not at `.instances` transparency as required by `dsimp`).

Such theorems are inferred automatically by `inferDefEqAttr`: any theorem that the old
`:= rfl` inference would have accepted is tagged `@[backward_defeq]`, and additionally
tagged `@[defeq]` when it also passes the stricter check at instance transparency.

`dsimp` ignores `@[backward_defeq]` theorems by default. Setting
`set_option backward.defeqAttrib.useBackward true` (typically scoped to a single proof
with `set_option ... in`) makes `dsimp` treat them like `@[defeq]` theorems, which
provides a local backwards-compatibility escape hatch for proofs broken by the stricter
inference.
-/
@[builtin_doc]
builtin_initialize backwardDefeqAttr : TagAttribute ←
  registerTagAttribute `backward_defeq
    "mark theorem as a definitional equality under the permissive pre-stricter-inference \
      rules, used by `dsimp` when `set_option backward.defeqAttrib.useBackward true`"
    (validate := validateBackwardDefEqAttr) (applicationTime := .afterTypeChecking)
    (asyncMode := .async .mainEnv)

/--
Marks the theorem as a definitional equality that can be used by `dsimp`.

The theorem must be an equality that holds at `.instances` transparency, the
transparency used by `dsimp`. If your theorem holds only at `.default`/`.all`
transparency, use `@[backward_defeq]` instead.

The attribute should be given before a `@[simp]` attribute to have effect.

When using the module system, an exported theorem can only be `@[defeq]` if all
definitions that need to be unfolded to prove the theorem are exported and exposed.

Tagging a theorem with `@[defeq]` automatically also tags it with `@[backward_defeq]`,
maintaining the invariant that `@[defeq]` theorems form a subset of `@[backward_defeq]`
theorems.
-/
@[builtin_doc]
builtin_initialize defeqAttr : TagAttribute ←
  registerTagAttribute `defeq "mark theorem as a definitional equality, to be used by `dsimp`"
    (validate := fun declName => do
      -- Validate the strict (instance-transparency) check. Then maintain the invariant
      -- `defeq ⊆ backward_defeq` by also tagging `backward_defeq`.
      validateDefEqAttr declName
      backwardDefeqAttr.setTag declName)
    (applicationTime := .afterTypeChecking)
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
        -- The application of a `defeq` or `backward_defeq` theorem is a `rfl` proof
        let env ← getEnv
        let c := proof.getAppFn.constName!
        return defeqAttr.hasTag env c || backwardDefeqAttr.hasTag env c
      else
        return false
    else
      return false

/--
For automatically generated theorems (equational theorems etc.), we tag the theorem with
the `defeq`/`backward_defeq` attributes based on its `rfl` proof:

* If the equation holds at `.instances` transparency (matching the transparency at which
  `dsimp` operates), we tag it with `@[defeq]`.
* Independently, if the equation holds under the more permissive legacy check (equivalent
  to `validateDefEqAttr`, i.e. at `.default` or `.all` transparency), we tag it with
  `@[backward_defeq]`.

In particular, every theorem that would have been tagged `@[defeq]` before the stricter
inference rules were introduced is now tagged `@[backward_defeq]`. Local backwards
compatibility can be restored with `set_option backward.defeqAttrib.useBackward true`.
-/
def inferDefEqAttr (declName : Name) : MetaM Unit := do
  withoutExporting do
    let info ← getConstInfo declName
    let isRfl ←
      if let some value := info.value? (allowOpaque := true) then
        isRflProofCore info.type value
      else
        pure false
    unless isRfl do return
    -- Strict check: defeq at instance transparency (as used by `dsimp`).
    let strict ← withEqLhsRhs info.type fun lhs rhs =>
      withReducibleAndInstances (isDefEq lhs rhs)
    -- Sanity-check: is the theorem also defeq at the permissive (`.default`/`.all`)
    -- transparency we use for `@[backward_defeq]`? If not, log the error that the
    -- legacy inference would have emitted — but still proceed to tag
    -- `@[backward_defeq]` unconditionally. The legacy (pre-PR) behavior tagged
    -- `@[defeq]` unconditionally whenever `isRflProofCore` returned true,
    -- regardless of whether the validation check passed, and we want to preserve
    -- exactly that set under `backward_defeq` so that `useBackward=true` reliably
    -- restores the old behavior.
    try
      withExporting (isExporting := !isPrivateName declName) do
        validateBackwardDefEqAttr declName
    catch e =>
      unless strict do
        logError m!"Theorem {declName} has a `rfl`-proof but could not be validated \
          as a definitional equality:{indentD e.toMessageData}"
    if strict then
      defeqAttr.setTag declName
    backwardDefeqAttr.setTag declName

/--
Diagnostic attribute used by `MutualDef` when `backward.inferDefEqOnRfl` is set. It runs
`inferDefEqAttr` (which tags the theorem with `[defeq]` when it holds at instance
transparency, and with `[backward_defeq]` when it merely holds at default/all
transparency). When `backward.inferDefEqOnRfl.trace` is also set, emits an info message
for each `:= rfl` theorem inferred to be `[defeq]`.

This attribute is internal: users should not apply it directly.
-/
@[builtin_doc]
builtin_initialize inferDefEqAttribute : TagAttribute ←
  registerTagAttribute `infer_defeq
    "internal diagnostic attribute used to infer `[defeq]` or `[backward_defeq]` for \
      `:= rfl` theorems"
    (validate := fun declName => do
      MetaM.run' <| inferDefEqAttr declName
      if backward.inferDefEqOnRfl.trace.get (← getOptions) then
        let env ← getEnv
        if defeqAttr.hasTag env declName then
          logInfo m!"`:= rfl` theorem `{declName}`: inferred @[defeq]")
    (applicationTime := .afterTypeChecking)
    (asyncMode := .async .mainEnv)
