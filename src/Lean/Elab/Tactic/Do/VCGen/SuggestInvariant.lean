/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Simp.Rewrite
import Lean.Util.OccursCheck
import Std.Do.Triple
import Std.Tactic.Do -- Needed for use of `mleave` in quote

public section

namespace Lean.Elab.Tactic.Do

open Lean Elab Tactic Meta
open Std.Do

private def duplicateMVar (m : MVarId) : MetaM MVarId := do
  let d ← m.getDecl
  let e ← mkFreshExprMVarAt d.lctx d.localInstances d.type d.kind d.userName d.numScopeArgs
  return e.mvarId!

private def eraseMacroScopesFromSyntax : Syntax → Syntax
  | Syntax.ident info rawVal val preresolved =>
    Syntax.ident info rawVal val.eraseMacroScopes preresolved
  | Syntax.node info kind args =>
    Syntax.node info kind (args.map eraseMacroScopesFromSyntax)
  | Syntax.atom info val => Syntax.atom info val
  | Syntax.missing => Syntax.missing

private def eraseMacroScopesFromTSyntax (syn : TSyntax name) : TSyntax name :=
  ⟨eraseMacroScopesFromSyntax syn.raw⟩

/--
Returns `some (ρ, σ)` if `doStateTupleTy` is of the form `MProd (Option ρ) σ` and every VC in `vcs`
uses the `Option ρ` component according to early return semantics.
* `ρ` is the type of early return (`Unit` in case of `break`)
* `σ` is an `n`-ary `MProd`, carrying the current value of the `let mut` variables.
  NB: When `n=0`, we have `MProd (Option ρ) PUnit` rather than `Option ρ`.
-/
private def hasEarlyReturn (vcs : Array MVarId) (inv : MVarId) (doStateTupleTy : Expr) : MetaM (Option (Expr × Expr)) := do
  if !(doStateTupleTy.isAppOf ``MProd) || doStateTupleTy.getAppNumArgs < 2 then return none
  let_expr Option ρ := doStateTupleTy.getArg! 0 | return none
  let σ := doStateTupleTy.getArg! 1

  -- The predicate on `doStateTupleTy` above is not sufficient; after all the user might just have
  -- introduced `let mut ret : Option α` and not use this variable according to "early return
  -- semantics", meaning that *if* `ret = some r` for some `r : ρ`, then the loop body returns
  -- `ForInStep.done (ret, ...)`. This is a property upheld by the `do` elaborator.
  --
  -- At this point, `mvcgen` has already run, so we do not see the syntax of the original loop body.
  -- However, we know that loop invariant lemmas such as `Spec.forIn_list` require that the
  -- invariant holds at `suffix = []` whenever the loop body returns `ForInStep.done`.
  -- Therefore, a sufficient condition for early return depends on whether all the VCs conform to
  -- the property:
  --
  -- > For any use of `?inv` of the form `?inv.fst (cursor, ⟨ret, ...⟩)` it is provable that either
  -- > `ret = none` or `cursor.suffix = []`.
  --
  -- Examples of VC goal types that uphold the property:
  -- * `(Prod.fst ?inv ({ «prefix» := [], suffix := l, property := ⋯ }, ⟨none, PUnit.unit⟩)).down`
  --   because `ret=none`
  -- * `(Prod.fst ?inv ({ «prefix» := pref✝ ++ [cur✝], suffix := suff✝, property := ⋯ }, ⟨none, PUnit.unit⟩)).down`
  --   because `ret=none`
  -- * `(Prod.fst ?inv ({ «prefix» := l, suffix := [], property := ⋯ }, ⟨some true, PUnit.unit⟩)).down`
  --   because `suffix = []`
  -- Example of a VC not fulfilling the property:
  -- * `(Prod.fst ?inv ({ «prefix» := pref✝ ++ [cur✝], suffix := suff✝, property := ⋯ }, ⟨some cur✝, ()⟩)).down`
  --   because `ret = some _` and `suffix = suff✝` and `suff✝` has instances other than `[]`.
  -- And similarly for unsimplified entailment `_ ⊢ₛ Prod.fst ?inv (cursor, ⟨some r, ...⟩)`:
  -- * `_ ⊢ₛ Prod.fst ?inv ({ «prefix» := pref✝ ++ [cur✝], suffix := suff✝, property := ⋯ }, ⟨some cur✝, ()⟩)`
  --   because `ret = some _` and `suffix = suff✝` and `suff✝` has instances other than `[]`.
  --
  -- Hence we check all VCs for the property above.

  for vc in vcs do
    -- No point in traversing the VC if the invariant is not used in it.
    let type ← instantiateMVars (← vc.getType)
    if ← occursCheck inv type then continue
    -- log m!"Looking at {vc}."
    let some spredTarget :=
      if type.isAppOf ``ULift.down && type.getAppNumArgs > 1 then some (type.getArg! 1)
      else if type.isAppOf ``Std.Tactic.Do.MGoalEntails && type.getAppNumArgs > 2 then some (type.getArg! 2)
      else if type.isAppOf ``SPred.entails && type.getAppNumArgs > 2 then some (type.getArg! 2)
      else none
      | continue
    -- `spredTarget` should be an overapplication of `Prod.fst`: `spredTarget = Prod.fst ?inv payload args`
    -- `args` can be non-empty when `σs` is non-empty.
    if !spredTarget.isAppOf ``Prod.fst then continue
    let args := spredTarget.getAppArgs
    -- log m!"Found Prod.fst. Args: {args}"
    if args.size < 4 then continue -- not an overapplication. Types should prohibit this case
    if args[2]! != mkMVar inv then continue -- not ?inv that is applied
    let payload := args[3]!
    -- log m!"Payload: {payload}"

    let_expr Prod.mk _ _ cursor acc := payload | return none -- NB: be conservative here
    let_expr List.Cursor.mk _α _l _pref suff _prop := cursor | return none -- dito
    -- The following check could be smarter. Essentially it tries to construct a proof that
    -- `suff = []` or `acc = (none, _)` and returns `none` upon failure.
    if !suff.isAppOf ``List.nil && !(acc.isAppOf ``MProd.mk && (acc.getArg! 2 |>.isAppOf ``Option.none)) then
      -- log m!"No early return! Not a `List.nil`: {suff} and not an `Option.none`: {acc.getArg! 2}"
      return none
  return (ρ, σ)

/--
Based on how a given metavariable `inv` binding a `Std.Do.Invariant` is used in the `vcs`, suggest
an initial assignment for `inv` to fill in for the user.
-/
def suggestInvariant (vcs : Array MVarId) (inv : MVarId) : TacticM Term := do
  -- We only synthesize suggestions for invariant subgoals
  let invType ← instantiateMVars (← inv.getType)
  let_expr _c@Std.Do.Invariant _α _l doStateTupleTy _ps := invType
    | throwError "Expected invariant type, got {invType}"

  -- Simplify the VCs a bit using `mleave`. Makes the job of the analysis below simpler.
  let vcs ← vcs.flatMapM fun vc =>
    try
      (·.toArray) <$> evalTacticAt (← `(tactic| mleave)) (← duplicateMVar vc)
    catch _e =>
      -- log m!"Failed to simplify {vc}: {_e.toMessageData}"
      pure #[vc]

  inv.withContext do
  -- When the loop has an early return, we want to suggest an invariant using `Invariant.withEarlyReturn`.
  if let some (_ρ, _σ) ← hasEarlyReturn vcs inv doStateTupleTy then
    -- log m!"Found early return for {inv}!"
    -- I tried to construct the Expr directly below, but elaborating and then delaborating `_` felt
    -- strange; furthermore calling the delaborator felt wrong. I might resurrect this code once
    -- the suggested invariants become deeper, though.
    --let us := c.constLevels!
    --withLocalDeclsDND #[(`xs, mkApp2 (mkConst ``List.Cursor us) α l), (`acc, σ)] fun _ => _
    --let onContinue ← withLocalDeclsDND #[(`xs, mkApp2 (mkConst ``List.Cursor us) α l), (`acc, σ)] fun _ => _dunno
    --let onReturn ← withLocalDeclsDND #[(`r, ρ), (`acc, σ)] fun _ => _dunno
    --let onExcept := mkConst ``ExceptConds.false us
    --let e := mkApp8 (mkConst ``Std.Do.Invariant.withEarlyReturn us) ps α l σ ρ onContinue onReturn onExcept
    -- how to delab `e : Expr` back into a `Term` to show to the user?
    let t ← ``(Invariant.withEarlyReturn (onReturn := fun r acc => _) (onContinue := fun xs acc => _))
    -- log m!"Suggested invariant: {toString t}"
    -- log m!"Suggested invariant: {toMessageData t}"
    return eraseMacroScopesFromTSyntax t
  eraseMacroScopesFromTSyntax <$> `(⇓ ⟨xs, acc⟩ => _)
