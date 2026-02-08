/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module
public import Lean.Elab
public import Lean.Meta
public import Lean.Parser
public import Lean.Expr
public meta import Lean.Elab
public meta import Lean.Meta

open Lean Parser Meta Elab Tactic Sym
open Lean.Elab.Tactic.Do.SpecAttr
open Std.Do

-- The following spec is necessary because the VC gen currently has no support for unfolding spec
-- theorems, which is what we usually do for `MonadState.get`.
@[spec]
theorem Spec.MonadState_get_StateT {m ps} [Monad m] [WPMonad m ps] {σ} {Q : PostCond σ (.arg σ ps)} :
    ⦃fun s => Q.fst s s⦄ get (m := StateT σ m) ⦃Q⦄ := by
  simp only [Triple, WP.get_MonadState, WP.get_StateT, SPred.entails.refl]

/-!
Creating backward rules for registered specifications
-/

namespace Lean.Elab.Tactic.Do.SpecAttr

/--
Look up a `SpecTheorem` in the `@[spec]` database. Picks the spec with the highest priority
among all specs that match the given program `e`.
-/
meta def SpecTheorems.findSpec (database : SpecTheorems) (e : Expr) : MetaM (Option SpecTheorem) := do
  let candidates ← database.specs.getMatch e
  let candidates := candidates.filter fun spec => !database.erased.contains spec.proof
  let specs := candidates.insertionSort fun s₁ s₂ => s₁.priority > s₂.priority
  return specs[0]?

/--
Create a backward rule for the `SpecTheorem` that was looked up in the database.
In order for the backward rule to apply, we need to instantiate both `m` and `ps` with the ones
given by the use site, and perhaps emit verification conditions for spec lemmas that would not
apply everywhere.

### General idea

Consider the spec theorem `Spec.bind`:
```
Spec.bind : ∀ {m : Type u → Type v} {ps : PostShape} [inst : Monad m] [inst_1 : WPMonad m ps]
  {α β : Type u} {x : m α} {f : α → m β} {Q : PostCond β ps},
  ⦃wp⟦x⟧ (fun a => wp⟦f a⟧ Q, Q.snd)⦄ (x >>= f) ⦃Q⦄
```
This theorem is already in "WP-form", so its postcondition `Q` is schematic (i.e., a ∀-bound var).
However, its precondition `wp⟦x⟧ ...` is not. Hence we must emit a VC for the precondition:
```
prf : ∀ {m : Type u → Type v} {ps : PostShape} [inst : Monad m] [inst_1 : WPMonad m ps]
  {α β : Type u} {x : m α} {f : α → m β} {Q : PostCond β ps}
  (P : Assertion ps) (hpre : P ⊢ₛ wp⟦x⟧ (fun a => wp⟦f a⟧ Q, Q.snd)),
  P ⊢ₛ wp⟦x >>= f⟧ Q
```
(Note that `P ⊢ₛ wp⟦x >>= f⟧ Q` is the definition of `⦃P⦄ (x >>= f) ⦃Q⦄`.)
Where `prf` is constructed by doing `SPred.entails.trans hpre spec` under the forall telescope.
The conclusion of this rule applies to any situation where `bind` is the top-level symbol in the
program.

Similarly, a VC is generated for the postcondition if it isn't schematic.

Furthermore, when there are excess state arguments `[s₁, ..., sₙ]` involved, we rather need to
specialize the backward rule for that:
```
... : ∀ {m : Type u → Type v} {ps : PostShape} [inst : Monad m] [inst_1 : WPMonad m ps]
  {α β : Type u} {x : m α} {f : α → m β} {Q : PostCond β ps}
  (P : Assertion ...) (hpre : P ⊢ₛ wp⟦x⟧ (fun a => wp⟦f a⟧ Q, Q.snd) s₁ ... sₙ),
  P ⊢ₛ wp⟦x >>= f⟧ Q s₁ ... sₙ
```

### Caching

It turns out we can cache backward rules for the cache key `(specThm, m, excessArgs.size)`.
This is very important for performance and helps getting rid of the overhead imposed by the
generality of `Std.Do`. We do that in the `VCGenM` wrapper `mkBackwardRuleFromSpecCached`.
Furthermore, in order to avoid re-checking the same proof in the kernel, we generate an auxiliary
lemma for the backward rule.

### Specialization and unfolding of `Std.Do` abbreviations and defs

It is unnecessary to use the `bind` rule in full generality. It is much more efficient to specialize
it for the particular monad, postshape and `WP` instance. In doing so we can also unfold many
`Std.Do` abbrevations, such as `Assertion ps` and `PostCond α ps`.
We do that by doing `unfoldReducible` on the forall telescope. The type for `StateM Nat` and one
excess state arg `s` becomes
```
prf : ∀ (α : Type) (x : StateT Nat Id α) (β : Type) (f : α → StateT Nat Id β)
        (Q : (β → Nat → ULift Prop) × ExceptConds (PostShape.arg Nat PostShape.pure)) (s : Nat)
        (P : ULift Prop) (hpre : P ⊢ₛ wp⟦x⟧ (fun a => wp⟦f a⟧ Q, Q.snd) s),
        P ⊢ₛ wp⟦x >>= f⟧ Q s
```
We are still investigating how to get rid of more unfolding overhead, such as for `wp` and
`List.rec`.
-/
meta def SpecTheorem.mkBackwardRuleFromSpec (specThm : SpecTheorem)
    (m σs ps instWP : Expr) (excessArgs : Array Expr) : SymM BackwardRule := do
  let preprocessExpr : Expr → SymM Expr := shareCommon <=< liftMetaM ∘ unfoldReducible
  let (xs, _bs, spec, specTy) ← specThm.proof.instantiate
  let_expr f@Triple m' ps' instWP' α prog P Q := specTy
    | liftMetaM <| throwError "target not a Triple application {specTy}"
  -- Using `isDefEq` here is fine. Firstly, it's cached, so performance isn't an issue.
  -- Secondly, the equated terms are never large. Thirdly, `isDefEqS` fails for type class instances.
  unless ← isDefEqGuarded m m' do throwError "Failed to equate {m} and {m'} when instantiating {spec}"
  unless ← isDefEqGuarded ps ps' do throwError "Failed to equate {ps} and {ps'} when instantiating {spec}"
  unless ← isDefEqGuarded instWP instWP' do throwError "Failed to equate {instWP} and {instWP'} when instantiating {spec}"

  -- We must ensure that P and Q are pattern variables so that the spec matches for every potential
  -- P and Q. We do so by introducing VCs accordingly.
  -- The following code could potentially be extracted into a definition at @[spec] attribute
  -- annotation time. That might help a bit with kernel checking time.
  let excessArgNamesTypes ← excessArgs.mapM fun arg =>
    return (← mkFreshUserName `s, ← Sym.inferType arg)
  let spec ← withLocalDeclsDND excessArgNamesTypes fun ss => do
    let needPreVC := !xs.contains P
    let needPostVC := !xs.contains Q
    let us := f.constLevels!
    let u := us[0]!
    let wp := mkApp5 (mkConst ``WP.wp us) m ps instWP α prog
    let wpApplyQ := mkApp4 (mkConst ``PredTrans.apply [u]) ps α wp Q  -- wp⟦prog⟧ Q
    let Pss := mkAppN P ss  -- P s₁ ... sₙ
    let typeP ← preprocessExpr (mkApp (mkConst ``SPred [u]) σs)
      -- Note that this is the type of `P s₁ ... sₙ`,
      -- which is `Assertion ps'`, but we don't know `ps'`
    let typeQ ← preprocessExpr (mkApp2 (mkConst ``PostCond [u]) α ps)
    let mut declInfos := #[]
    if needPreVC then
      let nmP' ← mkFreshUserName `P
      let nmHPre ← mkFreshUserName `hpre
      let entailment P' := preprocessExpr <| mkApp3 (mkConst ``SPred.entails [u]) σs P' Pss
      declInfos := #[(nmP', .default, fun _ => pure typeP),
                     (nmHPre, .default, fun xs => entailment xs[0]!)]
    if needPostVC then
      let nmQ' ← mkFreshUserName `Q
      let nmHPost ← mkFreshUserName `hpost
      let entailment Q' := pure <| mkApp3 (mkConst ``PostCond.entails [u]) ps Q Q'
      declInfos := declInfos ++
                   #[(nmQ', .default, fun _ => pure typeQ),
                     (nmHPost, .default, fun xs => entailment xs[0]!)]
    withLocalDecls declInfos fun ys => liftMetaM ∘ mkLambdaFVars (ss ++ ys) =<< do
      if !needPreVC && !needPostVC && excessArgs.isEmpty then
        -- Still need to unfold the triple in the spec type
        let entailment ← preprocessExpr <| mkApp3 (mkConst ``SPred.entails [u]) σs P wpApplyQ
        let prf ← mkExpectedTypeHint spec entailment
        -- check prf
        return prf
      let mut prf := spec
      let P := Pss  -- P s₁ ... sₙ
      let wpApplyQ := mkAppN wpApplyQ ss  -- wp⟦prog⟧ Q s₁ ... sₙ
      prf := mkAppN prf ss -- Turn `⦃P⦄ prog ⦃Q⦄` into `P s₁ ... sₙ ⊢ₛ wp⟦prog⟧ Q s₁ ... sₙ`
      let mut newP := P
      let mut newQ := Q
      if needPreVC then
        -- prf := hpre.trans prf
        let P' := ys[0]!
        let hpre := ys[1]!
        prf := mkApp6 (mkConst ``SPred.entails.trans [u]) σs P' P wpApplyQ hpre prf
        newP := P'
        -- check prf
      if needPostVC then
        -- prf := prf.trans <| (wp x).mono _ _ hpost
        let wp := mkApp5 (mkConst ``WP.wp f.constLevels!) m ps instWP α prog
        let Q' := ys[ys.size-2]!
        let hpost := ys[ys.size-1]!
        let wpApplyQ' := mkApp4 (mkConst ``PredTrans.apply [u]) ps α wp Q' -- wp⟦prog⟧ Q'
        let wpApplyQ' := mkAppN wpApplyQ' ss -- wp⟦prog⟧ Q' s₁ ... sₙ
        let hmono := mkApp6 (mkConst ``PredTrans.mono [u]) ps α wp Q Q' hpost
        let hmono := mkAppN hmono ss
        prf := mkApp6 (mkConst ``SPred.entails.trans [u]) σs newP wpApplyQ wpApplyQ' prf hmono
        newQ := Q'
        -- check prf
      return prf
  let res ← abstractMVars spec
  let type ← preprocessExpr (← Sym.inferType res.expr)
  trace[Elab.Tactic.Do.vcgen] "Type of new auxiliary spec apply theorem: {type}"
  let spec ← Meta.mkAuxLemma res.paramNames.toList type res.expr
  mkBackwardRuleFromDecl spec

end Lean.Elab.Tactic.Do.SpecAttr

/-!
VC generation
-/

public structure VCGen.Context where
  specThms : SpecTheorems
  /-- The backward rule for `SPred.entails_cons_intro`. -/
  entailsConsIntroRule : BackwardRule

public structure VCGen.State where
  /--
  A cache mapping registered SpecThms to their backward rule to apply.
  The particular rule depends on the theorem name, the monad and the number of excess state
  arguments that the weakest precondition target is applied to.
  -/
  specBackwardRuleCache : Std.HashMap (Name × Expr × Nat) BackwardRule := {}
  /--
  Holes of type `Invariant` that have been generated so far.
  -/
  invariants : Array MVarId := #[]
  /--
  The verification conditions that have been generated so far.
  -/
  vcs : Array MVarId := #[]

abbrev VCGenM := ReaderT VCGen.Context (StateRefT VCGen.State SymM)

namespace VCGen

@[inline]
meta def _root_.Std.HashMap.getDM [Monad m] [BEq α] [Hashable α]
    (cache : Std.HashMap α β) (key : α) (fallback : m β) : m (β × Std.HashMap α β) := do
  if let some b := cache.get? key then
    return (b, cache)
  let b ← fallback
  return (b, cache.insert key b)

/-- See the documentation for `SpecTheorem.mkBackwardRuleFromSpec` for more details. -/
meta def mkBackwardRuleFromSpecCached (specThm : SpecTheorem) (m σs ps instWP : Expr) (excessArgs : Array Expr) : VCGenM BackwardRule := do
  let mkRuleSlow := specThm.mkBackwardRuleFromSpec m σs ps instWP excessArgs
  let s ← get
  let .global decl := specThm.proof | mkRuleSlow
  let (rule, specBackwardRuleCache) ← s.specBackwardRuleCache.getDM (decl, m, excessArgs.size) mkRuleSlow
  set { s with specBackwardRuleCache }
  return rule

/-- Unfold `⦃P⦄ x ⦃Q⦄` into `P ⊢ₛ wp⟦x⟧ Q`. -/
meta def unfoldTriple (goal : MVarId) : SymM MVarId := goal.withContext do
  let type ← goal.getType
  unless type.isAppOf ``Triple do return goal
  let type ← unfoldDefinition type
  let goal ← goal.replaceTargetDefEq (← shareCommon type)
  preprocessMVar goal  -- need to reinstate subterm sharing

open Lean.Elab.Tactic.Do in
/--
Do a very targeted simplification to turn `P ⊢ₛ (fun _ => T, Q.snd).fst s` into `P ⊢ₛ T`.
This often arises as follows during backward reasoning:
```
  P ⊢ₛ wp⟦get >>= set⟧ Q
= P ⊢ₛ wp⟦get⟧ (fun a => wp⟦set a⟧ Q, Q.snd)
= P ⊢ₛ (fun s => (fun a => wp⟦set a⟧ Q, Q.snd).fst s s)
= P s ⊢ₛ (fun a => wp⟦set a⟧ Q, Q.snd).fst s s
-- This is where we simplify!
= P s ⊢ₛ wp⟦set s⟧ Q s
= P s ⊢ₛ Q.fst s s
-/
meta def simplifyTarget (goal : MVarId) : _root_.VCGenM MVarId := goal.withContext do
  let target ← goal.getType
  let_expr ent@SPred.entails σs P T := target | return goal
  let some T ← reduceProjBeta? T | return goal -- very slight simplification
  goal.replaceTargetDefEq (mkApp3 ent σs P T)

/--
Preprocess a goal, potentially closing it. This function assumes and preserves that the goal has is
normalized according to `Sym.preprocessMVar`.
-/
meta def preprocessGoal (goal : MVarId) : VCGenM (Option MVarId) := do
  let mut goal := goal
  if (← goal.getType).isForall then
    let IntrosResult.goal _ goal' ← Sym.intros goal | failure
    goal := goal'
  goal ← unfoldTriple goal
  goal ← simplifyTarget goal
  return goal

inductive SolveResult where
  /-- `target` was not of the form `H ⊢ₛ T`. -/
  | noEntailment (target : Expr)
  /-- The `T` in `H ⊢ₛ T` was not of the form `wp⟦e⟧ Q s₁ ... sₙ`. -/
  | noProgramFoundInTarget (T : Expr)
  /-- Don't know how to handle `e` in `H ⊢ₛ wp⟦e⟧ Q s₁ ... sₙ`. -/
  | noStrategyForProgram (e : Expr)
  /-- Did not find a spec for the `e` in `H ⊢ₛ wp⟦e⟧ Q s₁ ... sₙ`. -/
  | noSpecFoundForProgram (e : Expr)
  /-- Successfully discharged the goal. These are the subgoals. -/
  | goals (subgoals : List MVarId)

/--
The main VC generation function.
Looks at a goal of the form `P ⊢ₛ T`. Then
* If `T` is a lambda, introduce another state variable.
* If `T` is of the form `wp⟦e⟧ Q s₁ ... sₙ`, look up a spec theorem for `e`. Produce the backward
  rule to apply this spec theorem and then apply it ot the goal.
-/
meta def solve (goal : MVarId) : VCGenM SolveResult := goal.withContext do
  let target ← goal.getType
  trace[Elab.Tactic.Do.vcgen] "target: {target}"
  let_expr SPred.entails σs _H T := target | return .noEntailment target
  -- The goal is of the form `H ⊢ₛ T`. Look for program syntax in `T`.

  if T.isLambda then
    -- This happens after applying the `get` spec. We have `T = (fun s => (wp⟦e⟧ Q, Q.snd).fst s s)`.
    -- Do what `mIntroForall` does, that is, eta-expand. Note that this introduces an
    -- extra state arg `s` to reduce away the lambda.
    let .goals goals ← (← read).entailsConsIntroRule.apply goal
      | throwError "Applying {.ofConstName ``SPred.entails_cons_intro} to {target} failed. It should not."
    return .goals goals

  T.withApp fun apply args => do
  unless apply.isConstOf ``PredTrans.apply do return .noProgramFoundInTarget T
  let wp := args[2]!
  let_expr WP.wp m ps instWP _α e := wp | return .noProgramFoundInTarget T
  -- `T` is of the form `wp⟦e⟧ Q s₁ ... sₙ`, where `e` is the program.
  -- We call `s₁ ... sₙ` the excess state args; the backward rules need to account for these.
  -- Excess state args are introduced by the spec of `get` (see lambda case above).
  let excessArgs := args.drop 4
  let f := e.getAppFn
  withTraceNode `Elab.Tactic.Do.vcgen (msg := fun _ => return m!"Program: {e}") do

  -- Apply registered specifications.
  if f.isConst || f.isFVar then
    trace[Elab.Tactic.Do.vcgen] "Applying a spec for {e}. Excess args: {excessArgs}"
    let some thm ← (← read).specThms.findSpec e
      | return .noSpecFoundForProgram e
    let rule ← mkBackwardRuleFromSpecCached thm m σs ps instWP excessArgs
    let ApplyResult.goals goals ← rule.apply goal
      | throwError "Failed to apply rule {thm.proof} for {e}"
    return .goals goals

  return .noStrategyForProgram e

/--
Called when decomposing the goal further did not succeed; in this case we emit a VC for the goal.
-/
meta def emitVC (goal : MVarId) : VCGenM Unit := do
  let ty ← goal.getType
  goal.setKind .syntheticOpaque
  if ty.isAppOf ``Std.Do.Invariant then
    modify fun s => { s with invariants := s.invariants.push goal }
  else
    modify fun s => { s with vcs := s.vcs.push goal }

meta def work (goal : MVarId) : VCGenM Unit := do
  let mut worklist := Std.Queue.empty.enqueue (← preprocessMVar goal)
  -- while let some (goal, worklist') := worklist.dequeue? do
  repeat do
    let some (goal, worklist') := worklist.dequeue? | break
    worklist := worklist'
    let some goal ← preprocessGoal goal | continue
    let res ← solve goal
    match res with
    | .noEntailment .. | .noProgramFoundInTarget .. =>
      emitVC goal
    | .noSpecFoundForProgram prog =>
      throwError "No spec found for program {prog}"
    | .noStrategyForProgram prog =>
      throwError "Did not know how to decompose weakest precondition for {prog}"
    | .goals subgoals =>
      worklist := worklist.enqueueAll subgoals

public structure Result where
  invariants : Array MVarId
  vcs : Array MVarId

/--
Generate verification conditions for a goal of the form `P ⊢ₛ wp⟦e⟧ Q s₁ ... sₙ` by repeatedly
decomposing `e` using registered `@[spec]` theorems.
Return the VCs and invariant goals.
-/
public meta partial def main (goal : MVarId) (ctx : Context) : SymM Result := do
  let ((), state) ← StateRefT'.run (ReaderT.run (work goal) ctx) {}
  for h : idx in [:state.invariants.size] do
    let mv := state.invariants[idx]
    mv.setTag (Name.mkSimple ("inv" ++ toString (idx + 1)))
  for h : idx in [:state.vcs.size] do
    let mv := state.vcs[idx]
    mv.setTag (Name.mkSimple ("vc" ++ toString (idx + 1)) ++ (← mv.getTag).eraseMacroScopes)
  return { invariants := state.invariants, vcs := state.vcs }

/--
This function is best ignored; it's copied from `Lean.Elab.Tactic.Do.mkSpecContext`
and is more complex than necessary ATM.
-/
meta def mkSpecContext (lemmas : Syntax) (ignoreStarArg := false) : TacticM VCGen.Context := do
  let mut specThms ← getSpecTheorems
  let mut simpStuff := #[]
  let mut starArg := false
  for arg in lemmas[1].getSepArgs do
    if arg.getKind == ``simpErase then
      try
        -- Try and build SpecTheorems for the lemma to erase to see if it's
        -- meant to be interpreted by SpecTheorems. Otherwise fall back to SimpTheorems.
        let specThm ←
          if let some fvar ← Term.isLocalIdent? arg[1] then
            mkSpecTheoremFromLocal fvar.fvarId!
          else
            let id := arg[1]
            if let .ok declName ← observing (realizeGlobalConstNoOverloadWithInfo id) then
              mkSpecTheoremFromConst declName
            else
              withRef id <| throwUnknownConstant id.getId.eraseMacroScopes
        specThms := specThms.eraseCore specThm.proof
      catch _ =>
        simpStuff := simpStuff.push ⟨arg⟩ -- simp tracks its own erase stuff
    else if arg.getKind == ``simpLemma then
      unless arg[0].isNone && arg[1].isNone do
        -- When there is ←, →, ↑ or ↓ then this is for simp
        simpStuff := simpStuff.push ⟨arg⟩
        continue
      let term := arg[2]
      match ← Term.resolveId? term (withInfo := true) <|> Term.elabCDotFunctionAlias? ⟨term⟩ with
      | some (.const declName _) =>
        let info ← getConstInfo declName
        try
          let thm ← mkSpecTheoremFromConst declName
          specThms := addSpecTheoremEntry specThms thm
        catch _ =>
          simpStuff := simpStuff.push ⟨arg⟩
      | some (.fvar fvar) =>
        let decl ← getFVarLocalDecl (.fvar fvar)
        try
          let thm ← mkSpecTheoremFromLocal fvar
          specThms := addSpecTheoremEntry specThms thm
        catch _ =>
          simpStuff := simpStuff.push ⟨arg⟩
      | _ => withRef term <| throwError "Could not resolve {repr term}"
    else if arg.getKind == ``simpStar then
      starArg := true
      simpStuff := simpStuff.push ⟨arg⟩
    else
      throwUnsupportedSyntax
  -- Build a mock simp call to build a simp context that corresponds to `simp [simpStuff]`
  let stx ← `(tactic| simp +unfoldPartialApp -zeta [$(Syntax.TSepArray.ofElems simpStuff),*])
  -- logInfo s!"{stx}"
  let res ← mkSimpContext stx.raw
    (eraseLocal := false)
    (simpTheorems := getSpecSimpTheorems)
    (ignoreStarArg := ignoreStarArg)
  -- trace[Elab.Tactic.Do.vcgen] "{res.ctx.simpTheorems.map (·.toUnfold.toList)}"
  if starArg && !ignoreStarArg then
    let fvars ← getPropHyps
    for fvar in fvars do
      unless specThms.isErased (.local fvar) do
        try
          let thm ← mkSpecTheoremFromLocal fvar
          specThms := addSpecTheoremEntry specThms thm
        catch _ => continue
  let entailsConsIntroRule ← mkBackwardRuleFromDecl ``SPred.entails_cons_intro
  return { specThms, entailsConsIntroRule }

end VCGen

syntax (name := mvcgen') "mvcgen'"
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "] ")? : tactic

@[tactic mvcgen']
public meta def elabMVCGen' : Tactic := fun stx => withMainContext do
  let ctx ← VCGen.mkSpecContext stx[1]
  let goal ← getMainGoal
  let { invariants, vcs } ← SymM.run <| VCGen.main goal ctx
  replaceMainGoal (invariants ++ vcs).toList

/-!
Local tests for faster iteration:
-/

/-
def step (v : Nat) : StateM Nat Unit := do
  let s ← get
  set (s + v)
  let s ← get
  set (s - v)

def loop (n : Nat) : StateM Nat Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

set_option trace.Elab.Tactic.Do.vcgen true in
example : ⦃post⦄ loop 1 ⦃⇓_ => post⦄ := by
  intro post
  simp only [loop, step]
  mvcgen'
  grind
-/
