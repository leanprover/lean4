/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski

Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

prelude
public import Lean.Linter.Basic
public import Lean.Meta.ForEachExpr
public import Lean.Meta.Sorry
public import Lean.PrivateName
public import Lean.Server.InfoUtils
public import Lean.Linter.Util

public section

namespace Lean

namespace Expr
/--
Returns `true` if `type` is an application of a constant `decl` for which `p decl` is true, or a
forall with return type of the same form (i.e. of the form `∀ (x₀ : X₀) (x₁ : X₁) ⋯, decl ..` where
`p decl`).

Runs `cleanupAnnotations` on `type` and `forallE` bodies, and ignores metadata in applications.
-/
@[inline] private partial def isAppOrForallOfConstP (p : Name → Bool) (type : Expr) : Bool :=
  match type.cleanupAnnotations.getAppFn' with
  | .const n _ => p n
  | .forallE _ _ body _ => isAppOrForallOfConstP p body
  | _ => false

/--
Returns `true` if `e` includes a `forallE` instance binder with type satisfying `p`.

Cleans up annotations before traversing nested `forallE`s, and sees through `let`s.
-/
private partial def hasInstanceBinderOf (p : Expr → Bool) (e : Expr) : Bool :=
  match e.cleanupAnnotations with
  | .forallE _ type body bi => (bi.isInstImplicit && p type) || hasInstanceBinderOf p body
  | .letE _ _ _ body _ => hasInstanceBinderOf p body
  | _ => false

/--
Gets the indices `i` (in ascending order) of the binders of a nested `.forallE`,
`(x₀ : A₀) → (x₁ : A₁) → ⋯ → X`, such that
- the binder `[xᵢ : Aᵢ]` has `instImplicit` `binderInfo`
- `p Aᵢ` is `true`
- The rest of the type `(xᵢ₊₁ : Aᵢ₊₁) → ⋯ → X` does not depend on `xᵢ`. (It's in this sense that
  `xᵢ : Aᵢ` is "unused".)

Note that the argument to `p` may have loose bvars. This is a performance optimization.

This function runs `cleanupAnnotations` on each expression before examining it.

We see through `let`s, and do not increment the index when doing so. This behavior is compatible
with `forallBoundedTelescope`.
-/
private partial def getUnusedForallInstanceBinderIdxsWhere (p : Expr → Bool) (e : Expr) : Array Nat :=
  go e 0 #[]
where
  /-- Inspects `body`, and if it is a `.forallE` of an instance with type `type` such that `p type`
  is `true` and the remainder of the type does not depend on it, pushes the `current` index onto
  the accumulated array. -/
  go (body : Expr) (current : Nat) (acc : Array Nat) : Array Nat :=
    match body.cleanupAnnotations with
    | .forallE _ type body bi => go body (current+1) <|
      if bi.isInstImplicit && p type && !(body.hasLooseBVar 0) then
        acc.push current
      else
        acc
    /- See through `letE`, and just as in the interpretation of a bound provided to
    `forallBoundedTelescope`, do not increment the number of binders we've counted. -/
    | .letE _ _ _ body _ => go body current acc
    | _ => acc

end Expr

namespace Environment

/--
Like `findConstVal?`, but only finds the `ConstantVal` for `decl` in `env` if its kind satisfies
`p`. Otherwise, returns `none`.

Blocks on everything but the constant's body (if any), which is not accessible through the result.
-/
private def findConstValOfKind? (env : Environment) (p : ConstantKind → Bool) (decl : Name)
    (skipRealize := false) : Option ConstantVal := do
  let info ← env.findAsync? decl skipRealize
  if p info.kind then info.toConstantVal else none

/--
Like `findConstVal?`, but only finds the `ConstantVal` for `decl` in `env` if it is a theorem.

Blocks on everything but the constant's body (if any), which is not accessible through the result.
-/
private def findTheoremConstVal? (env : Environment) (decl : Name) (skipRealize := false) :
    Option ConstantVal :=
  env.findConstValOfKind? (· matches .thm) decl skipRealize

end Environment

namespace Linter.Extra
open Elab Command Meta Term

/--
Enables the 'unused `Decidable*` in type' linter, which lints against `Decidable*` instance
hypotheses in the types of theorems which are not used in the remainder of the type, and could
therefore be replaced with `classical` in the proof.

This linter fires only on theorems. (This includes `lemma`s and `instance`s of `Prop` classes.)
The constants recognised as `Decidable*` are `Decidable`, `DecidablePred`, `DecidableRel`,
`DecidableEq`, `DecidableLE`, and `DecidableLT`.
-/
register_builtin_option linter.extra.unusedDecidableInType : Bool := {
  defValue := false
  descr := "enable the unused `Decidable*` instance linter, which lints against `Decidable*` \
    instances in the hypotheses of theorems which are not used in the type, and can therefore be \
    replaced by a use of `classical` in the proof."
}

namespace UnusedDecidableInType

/--
Information about an unused parameter of some declaration.

`m!"{param}"` displays as `[{param.type?.get}] (#{param.idx + 1})` if `type?` is `some _`, and as
`parameter #{param.idx + 1}` as a failsafe if `type?` is `none`. (We always expect `type?` to be
`some _`, but allow `none` as a failsafe.)
-/
private structure Parameter where
  /-- The free variable of the parameter created in a telescope for logging.
  We always expect this to be `some _` normally, but allow `none` as a failsafe. -/
  fvar? : Option Expr
  /-- The type of the parameter created in a telescope for logging.
  We always expect this to be `some _` normally, but allow `none` as a failsafe. -/
  type? : Option Expr
  /-- The index of the parameter among the `forall` binders in the type (starting at 0). -/
  idx : Nat
  /-- Whether the parameter appears in a proof in the type. -/
  appearsInTypeProof : Bool

private instance : ToMessageData Parameter where
  toMessageData (param : Parameter) := Id.run do
    let mut msg := if let some type := param.type? then
      m!"[{type}] (#{param.idx + 1})"
    else
      m!"parameter #{param.idx + 1}"
    if param.appearsInTypeProof then
      msg := m!"{msg} (used in type, but only in a proof)"
    return msg

/--
Builds the message for an unused-instance-binder warning on `declName`.
The bracketed "outside of proofs" is only included if some parameter appears in a proof in the
type.
-/
private def unusedInstancesMsg (declName : Name) (unusedInstanceBinders : Array Parameter) :
    MessageData :=
  let anyAppearsInTypeProof := unusedInstanceBinders.any (·.appearsInTypeProof)
  let unusedInstanceBinders := unusedInstanceBinders.map toMessageData
  m!"`{.ofConstName declName}` does not use the following \
  {if unusedInstanceBinders.size = 1 then "hypothesis" else "hypotheses"} \
  in its type{if anyAppearsInTypeProof then " outside of proofs" else ""}:\
  {(unusedInstanceBinders.map (m!"\n  • {·}") |>.foldl (init := .nil) .compose)}"

/-- Information we keep track of when encountering a binder for an instance of concern. -/
private structure InstanceOfConcern where
  /-- The `FVarId` of the instance of concern within the current telescope. -/
  fvarId : FVarId
  /-- The index of the binder that this instance came from. The first binder is `0`, and we do not
  increment this index when seeing through `let`s. -/
  idx : Nat

/-- Collects free variables that do not appear in proofs. Ignores `sorry`s (and their types). -/
private def collectFVarsOutsideOfProofs (e : Expr) : StateRefT FVarIdSet MetaM Unit :=
  Meta.forEachExpr' e fun subExpr =>
    -- If it doesn't have an fvar, or it's a sorry, or it's a proof, don't descend further.
    pure (subExpr.hasFVar && !subExpr.isSorry) <&&> notM (Meta.isProof subExpr) <&&> do
      let .fvar fvarId := subExpr | return true
      modifyThe FVarIdSet (·.insert fvarId)
      return false

/--
Gets the indices `i` (in ascending order) of the binders of a nested `.forallE`,
`(x₀ : A₀) → (x₁ : A₁) → ⋯ → X`, such that
- the binder `[xᵢ : Aᵢ]` has `instImplicit` `binderInfo`
- `p Aᵢ` is `true`
- The rest of the type `(xᵢ₊₁ : Aᵢ₊₁) → ⋯ → X` does not depend on `xᵢ` outside of proofs.

This is like `Expr.getUnusedForallInstanceBinderIdxsWhere`, but ignores dependence that arises from
within proof terms.

The indices start at 0, and do not count `let`s.
-/
private partial def collectUnnecessaryInstanceBinderIdxsWhere (p : Expr → Bool) (e : Expr) :
    MetaM (Array Nat) := do
  let (instances, fvarIdSet) ← go e 0 #[] |>.run {}
  return instances.filterMap fun i => if fvarIdSet.contains i.fvarId then none else some i.idx
where
  /-- Enter foralls recursively, creating a telescope for binders which are instances of concern
  and instantiating all other bvars with `sorry`. The only free variables therefore arise from
  instances of concern which we want to track the usage of. -/
  go (e : Expr) (currentBinderIdx : Nat) (currentFVars : Array InstanceOfConcern) :
      StateRefT FVarIdSet MetaM (Array InstanceOfConcern) := do
    let e := e.cleanupAnnotations
    if h : e.isForall then
      collectFVarsOutsideOfProofs (e.forallDomain h)
      if e.binderInfo.isInstImplicit && p (e.forallDomain h) then
        forallBoundedTelescope e (some 1) fun fvar e => do
          let fvarId := fvar[0]!.fvarId!
          go e (currentBinderIdx + 1) (currentFVars.push { fvarId, idx := currentBinderIdx })
      else
        let e := (e.forallBody h).instantiate1 (← mkSorry (e.forallDomain h) false)
        go e (currentBinderIdx + 1) currentFVars
    else
      match e with
      | .letE _ type _ body _ =>
        collectFVarsOutsideOfProofs type
        let e := body.instantiate1 (← mkSorry type false)
        go e currentBinderIdx currentFVars
      | e =>
        collectFVarsOutsideOfProofs e
        return currentFVars

/--
Gathers instance hypotheses in the type of `decl` that are unused in the remainder of the type and
whose types satisfy `p`. (Does not consider the body of the declaration.) Collects them into an
`Array Parameter`, and if (and only if) this array is nonempty, feeds it to `logOnUnused`.
-/
private def onUnusedInstancesWhere (decl : ConstantVal) (p : Expr → Bool)
    (logOnUnused : Array Parameter → TermElabM Unit) : TermElabM Unit := do
  let unusedInstances ← collectUnnecessaryInstanceBinderIdxsWhere p decl.type
  if let some maxIdx := unusedInstances.back? then
    -- Only check for `sorry` in the "expensive" interactive case.
    unless decl.type.hasSorry do
      forallBoundedTelescope decl.type (some <| maxIdx + 1)
        (cleanupAnnotations := true) fun fvars _ => do
          /- If the binder is not unused in the type per se (by bvar dependence), but is considered
          unused by `collectUnnecessaryInstanceBinderIdxsWhere`, then it must have been used in a
          proof. We record this in the `appearsInTypeProof` field. -/
          let unusedEverywhereInstances := decl.type.getUnusedForallInstanceBinderIdxsWhere p
          let unusedParams : Array Parameter ← unusedInstances.mapM fun idx =>
            return {
              fvar? := fvars[idx]?
              type? := ← fvars[idx]?.mapM (inferType ·)
              idx
              appearsInTypeProof := !unusedEverywhereInstances.contains idx
            }
          logOnUnused unusedParams

/--
Get the declarations elaborated in the infotree `t` which are theorems according to the
environment. This includes e.g. `instance`s of `Prop` classes in addition to declarations declared
using the keyword `theorem` directly.
-/
private def getTheorems (t : InfoTree) (env : Environment) : List ConstantVal :=
  getDeclsByBody t |>.filterMap env.findTheoremConstVal?

/-- Checks if `type` is an application of (or forall ending in an application of) one of the
recognised `Decidable*` constants. -/
private def isDecidableVariant (type : Expr) : Bool :=
  type.isAppOrForallOfConstP fun n =>
    n == ``Decidable     ||
    n == ``DecidablePred ||
    n == ``DecidableRel  ||
    n == ``DecidableEq   ||
    n == ``DecidableLE   ||
    n == ``DecidableLT

@[inherit_doc linter.extra.unusedDecidableInType]
def unusedDecidableInTypeLinter : Linter where run := withSetOptionIn fun _ => do
  unless getLinterValue linter.extra.unusedDecidableInType (← getLinterOptions)
      && (← getInfoState).enabled do
    return
  if (← get).messages.hasErrors then
    return
  let env ← getEnv
  for t in ← getInfoTrees do
    /- Theorems in the `Decidable` namespace such as `Decidable.eq_or_ne` are allowed to depend
    on decidable instances without using them in the type. -/
    let thms := getTheorems t env |>.filter fun thm =>
      !((`Decidable).isPrefixOf (privateToUserName thm.name))
        && thm.type.hasInstanceBinderOf isDecidableVariant
    unless thms.isEmpty do liftTermElabM do for thm in thms do
      onUnusedInstancesWhere thm isDecidableVariant fun unusedParams => do
        logLintIf linter.extra.unusedDecidableInType (← getRef) m!"\
          {unusedInstancesMsg thm.name unusedParams}\n\n\
          Consider removing \
          {if unusedParams.size = 1 then "this hypothesis" else "these hypotheses"} \
          and using `classical` in the proof instead. \
          For terms, consider using `open scoped Classical in` at the term level (not the \
          command level)."

builtin_initialize addLinter unusedDecidableInTypeLinter

end UnusedDecidableInType
end Linter.Extra
end Lean
