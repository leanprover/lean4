/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module
public import Lean.Elab
public import Lean.Meta
public meta import Lean.Elab
public meta import Lean.Meta
public meta import Lean.Elab.Tactic.Do.VCGen.Split
public meta import VCGen.Context
public meta import VCGen.Reduce
public meta import VCGen.Util

open Lean Meta Elab Tactic Sym Sym.Internal
open Lean.Elab.Tactic.Do.SpecAttr
open Std.Do

/-!
Entailment-shaped goal decomposition: unfolding `Triple.of_entails_wp`, splitting
`PostCond.entails`/`ExceptConds.entails`, and the multi-phase `solveSPredEntails`
that drives `H ⊢ₛ T` to either a closed goal or a residual.
-/

namespace VCGen

/--
Unfold `⦃P⦄ x ⦃Q⦄` into `P ⊢ₛ wp⟦x⟧ Q` by applying `Tiple.of_wp`, ensuring that `PostShape.args ps`
is reduced.
-/
public meta def tripleOfWP (goal : MVarId) : _root_.VCGenM MVarId := goal.withContext do
  let .goals [goal] ← (← read).tripleOfEntailsWPRule.apply goal
    | throwError "Applying {.ofConstName ``Triple.of_entails_wp} to {goal} failed"
  goal.withContext do
    let target ← goal.getType
    let_expr ent@SPred.entails σs P Q := target | throwError "Expected SPred.entails: {target}"
    let σs ← shareCommonInc (← unfoldReducible σs)
    goal.replaceTargetDefEq (← Sym.Internal.mkAppS₃ ent σs P Q)

open Lean.Elab.Tactic.Do in
public meta def solveExceptCondsEntails (goal : MVarId) : _root_.VCGenM (Option MVarId) := goal.withContext do
  let target ← goal.getType
  let_expr ent@ExceptConds.entails ps P Q := target | return none
  let P ← reduceHead P
  let Q ← reduceHead Q
  let goal ← goal.replaceTargetDefEq (← Sym.Internal.mkAppS₃ ent ps P Q)
  if let .goals [] ← (← read).exceptCondsEntailsPureRule.apply goal then
    return none
  if let .goals [] ← (← read).exceptCondsEntailsFalseRule.apply goal then
    return none
  if let .goals [] ← (← read).exceptCondsEntailsTrueRule.apply goal then
    return none
  if let .goals [] ← (← read).exceptCondsEntailsRflRule.apply goal then
    return none
  return some goal

open Lean.Elab.Tactic.Do in
public meta def solvePostCondEntails (goal : MVarId) : _root_.VCGenM (Option (List MVarId)) := goal.withContext do
  let target ← goal.getType
  let_expr PostCond.entails _α _ps _P _Q := target | return none
  -- Try closing the whole entailment by reflexivity first.
  if let .goals [] ← (← read).postCondEntailsRflRule.apply goal then
    return some []
  -- Otherwise, decompose with `PostCond.entails.mk` into success + exception subgoals.
  let .goals [goal₁, goal₂] ← (← read).postCondEntailsMkRule.apply goal
    | throwError "Applying {.ofConstName ``PostCond.entails} to {target} failed. It should not."
  -- Try to discharge the exception subgoal by reflexivity. If that fails, leave it
  -- as a subgoal so it is emitted as a VC by the surrounding worklist loop.
  let extraGoal₂? ← goal₂.withContext (solveExceptCondsEntails goal₂)
  -- Normalize the success goal `∀ a, P a ⊢ₛ Q a`
  let goal₁ ← goal₁.withContext do
    let target ← goal₁.getType
    let .forallE x d b bi := target | throwError "Not a forall: {target}"
    let_expr ent@SPred.entails σs P Q := b | throwError "Not a SPred.entails: {target}"
    -- σs is of the form `PostShape.args ps` and we want to reduce it
    let σs ← shareCommonInc (← unfoldReducible σs)
    let b ← Sym.Internal.mkAppS₃ ent σs P Q
    let target ← Sym.Internal.MonadShareCommon.share1 <| .forallE x d b bi
    goal₁.replaceTargetDefEq target
  return goal₁ :: extraGoal₂?.toList

/--
Apply `SPred.entails_cons_intro` to introduce one state variable, then `introsSimp`,
then peel a leading `SPred.pure (σ::σs) φ s` from each side of `⊢ₛ` via
`apply_pure_cons_entails_l/r`. Returns `none` if no `entails_cons_intro` was applicable.

Performs the pure-cons cleanup at the exact iteration the state variable is introduced,
so the goal stays in canonical form throughout the eta-expansion loop.
-/
public meta def consIntroAndSimpStep (goal : MVarId) : VCGenM (Option MVarId) := do
  let ctx ← read
  let .goals [g'] ← ctx.entailsConsIntroRule.apply goal | return none
  let mut goal ← introsSimp g' m!"after applying {.ofConstName ``SPred.entails_cons_intro}"
  if let .goals [g''] ← ctx.applyPureConsEntailsLRule.apply goal then
    goal := g''
  if let .goals [g''] ← ctx.applyPureConsEntailsRRule.apply goal then
    goal := g''
  return some goal

public meta def neededStateIntro (thm : SpecTheoremNew) (goal : MVarId) (excessArgs : Array Expr) : VCGenM (Option MVarId) := do
  let .triple potential := thm.kind | return none
  let mut n := potential - excessArgs.size
  if n = 0 then return none
  let mut goal := goal
  while n > 0 do
    n := n - 1
    let some g ← consIntroAndSimpStep goal
      | throwError "Failed to introduce state at {goal} despite {n+1} spec potential"
    goal := g
  return some goal

/--
Break down `H ⊢ₛ T` as far as possible, reporting `none` when no progress was made.
1. If `H` is pure `⌜φ₁⌝`, turn the goal into `h : φ₁ ⊢ ⊢ₛ T`.
2. If *also* `T` is pure `⌜φ₂⌝`, turn the goal into `h : φ₁ ⊢ φ₂`, then exit.
3. Otherwise, `H` or `T` was not pure. We continue by introducing all state variables,
   `H s₁ ... sₙ ⊢ₛ T s₁ ... sₙ`. For a monomorphic monad stack, this will an entailment on
  `SPred []`. If either `H` or `T` was pure, `⌜·⌝`, state introduction preserves this.
4. Finally, turn `H ⊢ₛ T` into `h : H.down ⊢ T.down` (at `SPred []`).
5. If either `T` was pure `⌜φ₂⌝` (and `H` was not), we turn `T.down` into `φ₂`.
   (NB: If `H` was pure, then we have already lifted `φ₁` to the local context.)
-/
public meta def solveSPredEntails (goal : MVarId) : VCGenM (Option MVarId) := goal.withContext do
  let_expr SPred.entails _σs H T := (← goal.getType) | return none
  let mut progress := false
  let mut goal := goal

  -- First try to turn `⌜φ₁⌝ ⊢ₛ ⌜φ₂⌝` into `φ₁ → φ₂`.
  -- Do so in two steps:
  --   1. Move non-`True` `φ₁` to the local context, yielding `⌜True⌝ ⊢ₛ ⌜φ₂⌝` (which is `⊢ₛ ⌜φ₂⌝`).
  --   2. Eliminate `⊢ₛ ⌜φ₂⌝` to `φ₂`.
  -- If both succeed, we return `φ₁ → φ₂`. If 1. fails, we fall back to eta-expansion below.
  -- If 1. succeeds and 2. fails, we still continue with `φ₁` in the local context and eta-expand.
  let pureH : Option Expr := Prod.snd <$> H.app2? ``SPred.pure
  let pureT : Option Expr := Prod.snd <$> T.app2? ``SPred.pure

  let pureHNonTrue : Bool ←
    match pureH with
    | none => pure false
    | some h => not <$> isDefEqS h (mkConst ``True)
      if pureHNonTrue then
    let .goals [g'] ← (← read).pureElimRule.apply goal
      | throwError "Failed to apply {.ofConstName ``SPred.pure_elim'} to {← goal.getType}"
    progress := true
    goal ← introsSimp g' m!"after applying {.ofConstName ``SPred.pure_elim'}"

  if pureH.isSome && pureT.isSome then
    let .goals [g'] ← (← read).pureIntroRule.apply goal
      | throwError "Failed to apply {.ofConstName ``SPred.pure_intro} to {← goal.getType}"
    progress := true
    return some g'

  -- Now introduce states. If the monad stack is monomorphic, we will go all the way to `SPred []`
  -- and hence every entailment becomes pure.
  repeat do
    let some g' ← consIntroAndSimpStep goal | break
    progress := true
    goal := g'

  -- Now check again whether `H` became `⌜φ₁⌝` (it might have started as `fun s => ⌜φ₁⌝`).
  -- * If so, and `φ₁` is not `True`, we move `φ₁` to the local context and then
  --   turn `(h : φ₁)? ⊢ H ⊢ₛ T` into `⊢ T.down`.
  -- * Otherwise, we turn `⊢ H ⊢ₛ T` into `⊢ H.down → T.down` and
  --   introduce `H.down` (at `SPred []`).
  let_expr SPred.entails _σs H _T := (← goal.getType) | throwError "Not a SPred.entails: {← goal.getType}"
  if let some (_, h) := H.app2? ``SPred.pure then
    -- If `H` is `⌜True⌝`, we avoid introducing `h : True`.
    unless h matches .const ``True _ do
      if let .goals [g'] ← (← read).pureElimRule.apply goal then
        progress := true
        goal ← introsSimp g' m!"after applying {.ofConstName ``SPred.pure_elim'}"
    if let .goals [g'] ← (← read).pureIntroRule.apply goal then
      progress := true
      goal := g'
  else
    if let .goals [g'] ← (← read).entailsNilIntroRule.apply goal then
      progress := true
      goal ← introsSimp g' m!"after applying {.ofConstName ``SPred.entails_nil_intro}"

  -- Finally, if `T` is pure `⌜φ₂⌝`, we turn `T.down` into `φ₂`.
  if let .goals [g'] ← (← read).downPureIntroRule.apply goal then
    progress := true
    goal := g'

  if progress then
    return some goal
  else
    return none

end VCGen
