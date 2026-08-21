/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Tactic.Basic
public import Lean.Meta.Tactic.Simp.Types
import Lean.Meta.Tactic.Simp.Main
import Lean.Elab.Tactic.Do.VCGen.SuggestInvariant
import Std.WP.Triple.SpecLemmas

/-!
`invariants?` suggestion analysis for `vcgen`. Inspects how an `Invariant` metavariable
`?inv` is used in the verification conditions and derives an initial invariant to fill in.
-/

namespace Lean.Elab.Tactic.VCGen

open Lean Elab Tactic Meta
open Lean.Order
open Std.WP
open Lean.Elab.Tactic.Do (collectFVarsToRevert eraseQuoteMacroScopesFromTSyntax)

/-- A use of the invariant metavariable, of the form `?inv pref suff letMuts s₁ … sₙ`. -/
structure InvariantUse where
  /-- The elements consumed so far. -/
  prefixArg : Expr
  /-- The elements remaining. -/
  suffixArg : Expr
  /-- The `let mut` tuple argument. -/
  letMutsTuple : Expr
  /-- The leaves of the right-nested `Prod.mk` tree in `letMutsTuple`. -/
  letMuts : Array Expr
  /-- The state arguments that saturate `Pred`. -/
  stateArgs : Array Expr

/-- Classify `e` as a use `?inv pref suff letMuts s₁ … sₙ` of the invariant `inv`. -/
def classifyInvariantUse? (inv : MVarId) (e : Expr) : Option InvariantUse := Id.run do
  let e := e.consumeMData
  let args := e.getAppArgs
  unless e.getAppFn == mkMVar inv && args.size ≥ 3 do return none
  let mut letMuts := #[]
  let mut acc := args[2]!
  while acc.isAppOfArity ``Prod.mk 4 do
    letMuts := letMuts.push (acc.getArg! 2)
    acc := acc.getArg! 3
  letMuts := letMuts.push acc
  return some {
    prefixArg := args[0]!, suffixArg := args[1]!, letMutsTuple := args[2]!,
    letMuts, stateArgs := args[3:].toArray }

/-- The decomposed type of a VC: a `Prop` goal with its hypothesis types, or a lattice
entailment `lhs ⊑ rhs`. -/
inductive VCShape where
  | prop (hyps : Array Expr) (target : Expr)
  | entails (lhs rhs : Expr)

/-- Decompose the type of `vc` into a `VCShape`. On an entailment whose right-hand side is a
stuck `match` on a `ForInStep` literal, `whnf` selects the live arm so a use of `?inv` becomes
visible. -/
def getVCShape (inv : MVarId) (vc : MVarId) : MetaM VCShape := vc.withContext do
  let target := (← instantiateMVars (← vc.getType)).consumeMData
  if let some (_, _, lhs, rhs) := target.app4? ``Lean.Order.PartialOrder.rel then
    let mut rhs := rhs
    if (classifyInvariantUse? inv rhs).isNone && (rhs.find? (· == mkMVar inv)).isSome then
      rhs ← whnf rhs
    return .entails lhs rhs
  let mut hyps := #[]
  for decl in (← getLCtx) do
    unless decl.isImplementationDetail do
      hyps := hyps.push (← instantiateMVars decl.type)
  return .prop hyps target

/-- Returns `some (ρ, σ)` if `letMutsTy` is `Option ρ × σ` and every VC target use conforms to
early return semantics: a first component other than `none` only occurs at `suff = []`. -/
def hasEarlyReturn (letMutsTy : Expr) (targetUses : Array InvariantUse) (hasUnknownUse : Bool) :
    Option (Expr × Expr) := Id.run do
  if hasUnknownUse then return none
  let some (fstTy, σ) := letMutsTy.app2? ``Prod | return none
  let some ρ := fstTy.app1? ``Option | return none
  for use in targetUses do
    if use.suffixArg.isAppOf ``List.nil then continue
    unless use.letMutsTuple.isAppOfArity ``Prod.mk 4 do return none
    unless use.letMuts[0]!.isAppOf ``Option.none do return none
  return some (ρ, σ)

/-- Map the right-nested `Prod.mk` tree `tuple` (and each of its sub-tuples and fvar leaves)
to the corresponding projection of `proj`. -/
partial def tupleReplacements (tuple proj : Expr) : MetaM (Array (Expr × Expr)) := do
  if tuple.isAppOfArity ``Prod.mk 4 then
    let fst ← mkProjection proj `fst
    let snd ← mkProjection proj `snd
    return #[(tuple, proj)]
      ++ (← tupleReplacements (tuple.getArg! 2) fst)
      ++ (← tupleReplacements (tuple.getArg! 3) snd)
  else if tuple.isFVar then
    return #[(tuple, proj)]
  else
    return #[]

/-- Rewrite the `let mut` tuple of `use` (and each of its components) to the corresponding
projection of `letMutsVar`, and each state argument to its binder in `stateVars`. -/
def substLetMutsAndStates (letMutsVar : Expr) (stateVars : Array Expr) (use : InvariantUse)
    (e : Expr) : MetaM Expr := do
  let mut map ← tupleReplacements use.letMutsTuple letMutsVar
  for (arg, var) in use.stateArgs.zip stateVars do
    if arg.isFVar then
      map := map.push (arg, var)
  let replacements := map
  return e.replace fun sub => replacements.findSome? fun (k, v) => if k == sub then some v else none

/-- Turn the fvars of `e` outside `dontRevert` (and their forward dependencies) into universal
quantifiers and `let`s, so `e` makes sense with only the `dontRevert` fvars in scope. -/
def revertPropFVarsExcept (e : Expr) (dontRevert : FVarId → Bool) : MetaM Expr := do
  let xs ← collectFVarsToRevert e dontRevert
  mkForallFVars xs e

/-- The collected hints for instantiating an invariant, in terms of the shared binders. -/
structure InvariantHints where
  /-- The `let mut` tuple at loop entry, zeta-expanded. -/
  init : Expr
  /-- The `[]` expression from the entry use, for `pref = []`. -/
  prefixNil : Expr
  /-- The `[]` expression from an exit use, for `suff = []`. -/
  suffixNil : Expr
  /-- The conjunction of the exit conditions, over `letMutsVar` and `stateVars`.
  A `Prop` for applied uses, a `Pred` for entailment uses. -/
  exitPred : Expr

/-- Scan the `vcs` for uses of `inv` and derive `InvariantHints` phrased in terms of
`letMutsVar` and `stateVars`. `lattice` selects between `Prop` VCs and entailment VCs. -/
def collectInvariantHints (vcs : Array (MVarId × VCShape)) (inv : MVarId) (lattice : Bool)
    (letMutsVar : Expr) (stateVars : Array Expr) : MetaM (Option InvariantHints) := do
  let invLCtx ← inv.withContext getLCtx
  let mut init? := none
  let mut prefixNil? := none
  let mut suffixNil? := none
  let mut exitPreds := #[]
  for (vc, shape) in vcs do
    match shape, lattice with
    | .prop hyps target, false =>
      if let some use := classifyInvariantUse? inv target then
        if use.prefixArg.isAppOf ``List.nil then
          init? := some (← vc.withContext <| zetaReduce use.letMutsTuple)
          prefixNil? := some use.prefixArg
      for hyp in hyps do
        let some use := classifyInvariantUse? inv hyp | continue
        unless use.suffixArg.isAppOf ``List.nil do continue
        let componentFVars := use.letMuts.filterMap fun e => if e.isFVar then some e.fvarId! else none
        let stateFVars := use.stateArgs.filterMap fun e => if e.isFVar then some e.fvarId! else none
        let dontRevert := fun fvarId =>
          componentFVars.contains fvarId || stateFVars.contains fvarId || invLCtx.contains fvarId
        let reverted ← vc.withContext <| revertPropFVarsExcept target dontRevert
        exitPreds := exitPreds.push (← substLetMutsAndStates letMutsVar stateVars use reverted)
        suffixNil? := suffixNil?.orElse fun _ => some use.suffixArg
    | .entails lhs rhs, true =>
      if let some use := classifyInvariantUse? inv rhs then
        if use.prefixArg.isAppOf ``List.nil then
          init? := some (← vc.withContext <| zetaReduce use.letMutsTuple)
          prefixNil? := some use.prefixArg
      if let some use := classifyInvariantUse? inv lhs then
        if use.suffixArg.isAppOf ``List.nil && (classifyInvariantUse? inv rhs).isNone then
          let componentFVars := use.letMuts.filterMap fun e => if e.isFVar then some e.fvarId! else none
          let dontRevert := fun fvarId =>
            componentFVars.contains fvarId || invLCtx.contains fvarId
          -- On a pure right-hand side `⌜p⌝`, revert the VC-local fvars inside `p`; another
          -- right-hand side is usable only when it has no VC-local fvars.
          let clause? ← vc.withContext do
            if rhs.isAppOfArity ``Lean.Order.CompleteLattice.ofProp 3 then
              let p ← revertPropFVarsExcept (rhs.getArg! 2) dontRevert
              return some (rhs.withApp fun f args => mkApp3 f args[0]! args[1]! p)
            else if (← collectFVarsToRevert rhs dontRevert).isEmpty then
              return some rhs
            else
              return none
          if let some clause := clause? then
            exitPreds := exitPreds.push (← substLetMutsAndStates letMutsVar stateVars use clause)
            suffixNil? := suffixNil?.orElse fun _ => some use.suffixArg
    | _, _ => continue
  let some init := init? | return none
  let some prefixNil := prefixNil? | return none
  let some suffixNil := suffixNil? | return none
  if exitPreds.isEmpty then return none
  let mut exitPred := exitPreds[0]!
  for p in exitPreds[1:] do
    exitPred ← if lattice then mkAppM ``Lean.Order.meet #[exitPred, p] else pure (mkAnd exitPred p)
  return some { init, prefixNil, suffixNil, exitPred }

/-- Embed the proposition `p` into the assertion lattice `Pred` as `⌜p⌝`. -/
def mkOfProp (Pred p : Expr) : MetaM Expr :=
  mkAppOptM ``Lean.Order.CompleteLattice.ofProp #[some Pred, none, some p]

/--
Fold `⌜·⌝` outward through `⊓` and `⊔`: `⌜a⌝ ⊓ (⌜b⌝ ⊔ ⌜c⌝)` becomes `⌜a ∧ (b ∨ c)⌝`.
Purely syntactic, on a best-effort basis.
-/
partial def tryHoistPure (Pred : Expr) (e : Expr) : MetaM Expr := do
  match go e with
  | some p => mkOfProp Pred p
  | none => return e
where
  go (e : Expr) : Option Expr := do
    if e.isAppOfArity ``Lean.Order.CompleteLattice.ofProp 3 then
      return e.getArg! 2
    if e.isAppOfArity ``Lean.Order.meet 4 then
      return mkAnd (← go (e.getArg! 2)) (← go (e.getArg! 3))
    if e.isAppOfArity ``Lean.Order.join 4 then
      return mkOr (← go (e.getArg! 2)) (← go (e.getArg! 3))
    failure

/-- Simplify a clause of a suggestion with the default simp set, e.g. to reduce the
specialization of an exit condition to the `none`/`some` case of an early return. -/
def simpClause (e : Expr) : MetaM Expr := do
  let ctx ← Simp.mkContext
    (config := {})
    (simpTheorems := #[(← Meta.getSimpTheorems)])
    (congrTheorems := (← Meta.getSimpCongrTheorems))
  let simprocs ← ({} : Simp.SimprocsArray).add `reduceCtorEq false
  let (res, _) ← Lean.Meta.simp e ctx simprocs
  return res.expr

/-- Peel `n` state argument types off the assertion lattice `Pred`. -/
def peelStateTypes? (Pred : Expr) (n : Nat) : MetaM (Option (Array Expr)) := do
  let mut tys := #[]
  let mut cur := Pred
  for _ in [:n] do
    let .forallE _ ty body _ ← whnf cur | return none
    if body.hasLooseBVars then return none
    tys := tys.push ty
    cur := body
  return some tys

/-- `(pref = [] ∧ letMuts = init) ∨ (suff = [] ∧ exit)`, in `Prop` or in the lattice `Pred`. -/
def mkClause (lattice : Bool) (Pred prefVar suffVar letMutsVar : Expr) (hints : InvariantHints) :
    MetaM Expr := do
  let prefixEq ← mkEq prefVar hints.prefixNil
  let initEq ← mkEq letMutsVar hints.init
  let suffixEq ← mkEq suffVar hints.suffixNil
  if lattice then
    let entry ← mkAppM ``Lean.Order.meet #[← mkOfProp Pred prefixEq, ← mkOfProp Pred initEq]
    let exit ← mkAppM ``Lean.Order.meet #[← mkOfProp Pred suffixEq, hints.exitPred]
    tryHoistPure Pred (← mkAppM ``Lean.Order.join #[entry, exit])
  else
    return mkOr (mkAnd prefixEq initEq) (mkAnd suffixEq hints.exitPred)

/-- Delaborate `fun xs… => body` into a `Term`. -/
def delabLam (xs : Array Expr) (body : Expr) : MetaM Term := do
  Lean.PrettyPrinter.delab (← mkLambdaFVars xs body)

/--
Based on how the metavariable `inv` binding a `Std.WP.Invariant` is used in the `vcs`, suggest
an initial assignment for `inv` to fill in for the user.
-/
public def suggestInvariant (vcs : Array MVarId) (inv : MVarId) : TacticM Term := do
  let invType := (← instantiateMVars (← inv.getType)).consumeMData
  let_expr c@Std.WP.Invariant α letMutsTy Pred := invType
    | throwError "expected an `Invariant` goal, got{indentExpr invType}"
  let u₁ := c.constLevels![0]!
  inv.withContext do
  let shapes ← vcs.mapM fun vc => return (vc, ← getVCShape inv vc)
  -- Collect the uses in target position (`Prop` targets and entailment right-hand sides).
  let mut targetUses := #[]
  let mut hasUnknownUse := false
  let mut lattice := false
  for (_, shape) in shapes do
    let target := match shape with | .prop _ t => t | .entails _ r => r
    if let some use := classifyInvariantUse? inv target then
      targetUses := targetUses.push use
      if shape matches .entails .. then lattice := true
    else if target.find? (· == mkMVar inv) |>.isSome then
      hasUnknownUse := true
  let stateArity := if lattice then 0 else targetUses.foldl (max · ·.stateArgs.size) 0
  let some stateTys ← peelStateTypes? Pred stateArity
    | throwError "could not determine the state arguments of {Pred}"
  let listTy := mkApp (mkConst ``List [u₁]) α
  withLocalDeclD `pref listTy fun prefVar =>
  withLocalDeclD `suff listTy fun suffVar =>
  withLocalDeclD `letMuts letMutsTy fun letMutsVar => do
  let stateNames := if stateArity == 1 then #[`s] else
    (Array.range stateArity).map fun i => Name.mkSimple s!"s{i + 1}"
  withLocalDeclsDND (stateNames.zip stateTys) fun stateVars => do
  let hints? ← collectInvariantHints shapes inv lattice letMutsVar stateVars
  eraseQuoteMacroScopesFromTSyntax <$> do
  if let some (ρ, σ) := hasEarlyReturn letMutsTy targetUses hasUnknownUse then
    -- Suggest an invariant using `Invariant.withEarlyReturnNewDo`.
    withLocalDeclD `r ρ fun rVar =>
    withLocalDeclD `letMuts σ fun letMutsσ => do
    match hints? with
    | some hints =>
      let clause ← mkClause lattice Pred prefVar suffVar letMutsVar hints
      let noneTup ← mkAppM ``Prod.mk #[← mkNone ρ, letMutsσ]
      let someTup ← mkAppM ``Prod.mk #[← mkSome ρ rVar, letMutsσ]
      let onContinue ← simpClause (clause.replaceFVar letMutsVar noneTup)
      let onReturn ← simpClause (← tryHoistPure Pred (hints.exitPred.replaceFVar letMutsVar someTup))
      let c ← delabLam (#[prefVar, suffVar, letMutsσ] ++ stateVars) onContinue
      let r ← delabLam (#[rVar, letMutsσ] ++ stateVars) onReturn
      `(Invariant.withEarlyReturnNewDo (onContinue := $c) (onReturn := $r))
    | none =>
      `(Invariant.withEarlyReturnNewDo (onContinue := fun pref suff letMuts => _)
          (onReturn := fun r letMuts => _))
  else if let some hints := hints? then
    let clause ← mkClause lattice Pred prefVar suffVar letMutsVar hints
    delabLam (#[prefVar, suffVar, letMutsVar] ++ stateVars) clause
  else
    `(fun pref suff letMuts => _)

end Lean.Elab.Tactic.VCGen
