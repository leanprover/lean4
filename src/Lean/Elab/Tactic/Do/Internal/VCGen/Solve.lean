/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf, Vladimir Gladshtein
-/
module

prelude
public import Lean.Elab.Tactic.Do.Internal.VCGen.Context
public import Lean.Elab.Tactic.Do.Internal.VCGen.RuleCache
public import Lean.Elab.Tactic.Do.Internal.VCGen.Entails
public import Lean.Meta.Sym.InstantiateS
import Lean.Meta.Sym.InferType
import Lean.Meta.Sym.InstantiateMVarsS

open Lean Meta Elab Tactic Sym Sym.Internal
open Lean.Elab.Tactic.Do.Internal.SpecAttr
open Lean.Elab.Tactic.Do.Internal
open Std.Internal.Do Lean.Order

namespace Lean.Elab.Tactic.Do.Internal

/-!
The main `solve` step. Runs once per worklist iteration and either fully
decomposes the current goal into subgoals, or reports why no further
progress is possible (`SolveResult`).
-/

namespace VCGen

/-- The reason why no further VC generation progress is possible on the current goal. -/
public inductive SolveResult.StopReason where
  /-- Out of fuel. -/
  | outOfFuel
  /-- `until <pat>` matched. -/
  | untilPatternMatched (m : Expr)
  /-- The target was not of the form `pre ⊑ rhs`. -/
  | noEntailment (target : Expr)
  /-- The target was of the form `pre ⊑ rhs`, but we couldn't make further progress. -/
  | noProgress (pre rhs : Expr)
  /-- No spec was found for the program `e` in `pre ⊑ wp e post epost s₁ ... sₙ`. Candidates
  were `thms`, but none matched the monad. Reached only when `errorOnMissingSpec` is `false`. -/
  | noSpecFound (e : Expr) (monad : Expr) (thms : Array SpecTheorem)

/-- The result of one `solve` step of VC generation. -/
public inductive SolveResult where
  /-- Successfully decomposed the goal. Each subgoal carries its own scope. -/
  | goals (subgoals : List (VCGen.Scope × MVarId))
  /-- No further progress possible; emit the current goal as a VC. -/
  | stop (reason : SolveResult.StopReason)

/-- Decomposition result whose subgoals all share `scope`. -/
public def SolveResult.goalsInScope (scope : VCGen.Scope) (subgoals : List MVarId) : SolveResult :=
  .goals (subgoals.map (scope, ·))

private def isDuplicable (e : Expr) : Bool := match e with
  | .bvar .. | .mvar .. | .fvar .. | .const .. | .lit .. | .sort .. => true
  | .mdata _ e | .proj _ _ e => isDuplicable e
  | .lam .. | .forallE .. | .letE .. => false
  | .app .. => e.isAppOf ``OfNat.ofNat

/-- Strip an annotation, such as the `noImplicitLambda` metadata a tactic `have`/`let`/`suffices`
leaves on the goal, so later strategies and the backward rules they invoke see the bare target. -/
private def consumeMData? (goal : MVarId) (target : Expr) : VCGenM (Option MVarId) := do
  unless target.isMData do return none
  return some (← goal.replaceTargetDefEqFast target.consumeMData)

/-- Strategy 1: simp the target, then introduce binders if the target is a `∀`. -/
private def forallIntro? (goal : MVarId) (target : Expr) : VCGenM (Option (List MVarId)) := do
  unless target.isForall do return none
  let (goal, simped) ← match ← simpGoalTelescope goal with
    | .closed => return some []
    | .goal goal' => pure (goal', true)
    | .noProgress => pure (goal, false)
  let goal' ← introsHygienic goal
  if !simped && goal' == goal then
    throwError "Failed to intro forall target {goal}"
  return some [goal']

/-- Strategy 2: zeta-substitute a duplicable top-level `let` in the target, otherwise
introduce it into the local context. -/
private def targetLetIntro? (goal : MVarId) (target : Expr) : VCGenM (Option MVarId) := do
  let .letE name _ val body _ := target | return none
  if isDuplicable val then
    trace[Elab.Tactic.Do.vcgen] "let-zeta-dup: {name}"
    return some (← goal.replaceTargetDefEqFast (← Sym.instantiateRevBetaS body #[val]))
  else
    trace[Elab.Tactic.Do.vcgen] "let-intro: {name}"
    return some (← introsHygienic goal)

/-- Strategy 3: unfold a `Triple` target into the underlying lattice entailment. -/
private def tripleUnfold? (goal : MVarId) (target : Expr) : VCGenM (Option MVarId) := do
  unless target.isAppOf ``Triple do return none
  return some (← unfoldTriple goal)

/-- Strategy 3b: turn a bare `wp` application target (a `Prop`) into `⊤ ⊑ wp …`. Entry-point
goals produced by the `of_wp_run_eq` lemmas have this shape. -/
private def bareWPToLe? (goal : MVarId) (target : Expr) : VCGenM (Option MVarId) := do
  let some _ := isWPApp? target | return none
  let newTarget ← mkAppM ``PartialOrder.rel #[← mkAppOptM ``Lean.Order.top #[mkSort 0, none], target]
  let newTarget ← shareCommon newTarget
  let g ← liftMetaM <| mkFreshExprSyntheticOpaqueMVar newTarget
  goal.assign (mkApp2 (mkConst ``Lean.Order.of_top_le_prop) target g)
  return some g.mvarId!

/-- Strategy 4: close a reflexive entailment `pre ⊑ pre` by applying `PartialOrder.rel_refl`.
Runs before the precondition lift so a spec handoff `pre ⊑ specPre` closes by unification rather
than an assumption search. The pattern matcher keeps synthetic-opaque invariant holes rigid, so
`⊤ ⊑ ?inv args` is left untouched. -/
private def rfl? (goal : MVarId) : VCGenM (Option (List MVarId)) := do
  -- Reflexivity is best-effort: the unifier throws on an un-decomposed program-head `let` (e.g. a
  -- chained `__do_jp`) rather than reporting "not equal". A throw leaves `goal` unassigned, so
  -- treat it as "not reflexive here" and let `wp` decomposition handle the `let`.
  let .goals gs ← try (← read).backwardRules.refl.apply goal catch _ => return none
    | return none
  trace[Elab.Tactic.Do.vcgen] "Solved by rfl {goal}"
  return some gs

/-- The most recently lifted pure precondition (cached in `Scope.lastLiftedPre?`) whose type is
the same hash-consed expression as `e`, or `none`. Must run in `goal`'s context. -/
private def liftedPreFor? (scope : VCGen.Scope) (e : Expr) : VCGenM (Option LocalDecl) := do
  let some fvarId := scope.lastLiftedPre? | return none
  let some hyp := (← getLCtx).find? fvarId | return none
  unless isSameExpr e hyp.type do return none
  trace[Elab.Tactic.Do.vcgen] "Solved by lifted hypothesis {hyp.userName}"
  return some hyp

/-- Strategy 10: close `pre ⊑ φ` on the `Prop` lattice against the most recently lifted pure
precondition. Runs after lattice decomposition, so `φ` is an opaque proposition rather than a
lattice connective. This is one comparison against one hypothesis, not an assumption search. -/
private def liftedHyp? (scope : VCGen.Scope) (goal : MVarId) (α pre rhs : Expr) :
    VCGenM (Option (List MVarId)) :=
  goal.withContext do
    unless α.isProp do return none
    let some hyp ← liftedPreFor? scope rhs | return none
    goal.assign (← mkAppM ``Lean.Order.le_of_right #[pre, rhs, hyp.toExpr])
    return some []

/-- Close a bare `Prop` residual, such as the subgoal of the `⌜φ⌝` lattice rule, against the
most recently lifted pure precondition. Runs when the target is not a lattice entailment,
just before it would be classified as a VC. -/
private def liftedHypBare? (scope : VCGen.Scope) (goal : MVarId) (target : Expr) :
    VCGenM (Option (List MVarId)) :=
  goal.withContext do
    let some hyp ← liftedPreFor? scope target | return none
    goal.assign hyp.toExpr
    return some []

/-- Strategy 5: cancel a redundant `P ⊓ ⊤` precondition via `meet_top_le_of_le`, leaving `P ⊑ rhs`.
Such a precondition arises when `himp_complete` splits `⊤ ⊑ a ⇨ b` into `a ⊓ ⊤ ⊑ b`. -/
private def stripMeetTopPre? (goal : MVarId) (pre : Expr) : VCGenM (Option MVarId) := do
  let_expr Lean.Order.meet _l _inst _P top := pre | return none
  unless top.isAppOf ``Lean.Order.top do return none
  let .goals [g] ← (← read).backwardRules.meetTop.applyChecked goal
    | throwError "Failed to cancel the `⊓ ⊤` precondition of {goal}"
  return some g

/-- Strategy 5: lift an embedded pure precondition `⌜φ⌝` into the local context, leaving `⊤`
as the residual precondition. Runs before state-argument introduction, which would otherwise
leave `⌜φ⌝` applied to the introduced arguments. Returns the new goal and the hypothesis. -/
private def ofPropPreIntro? (goal : MVarId) (pre : Expr) : VCGenM (Option (MVarId × FVarId)) := do
  let_expr CompleteLattice.ofProp _l _inst φ := pre | return none
  if φ.isTrue then return none
  return some (← introPre (← read).backwardRules.ofPropPreIntro goal)

/-- Strategy 7: move a bare `Prop` precondition `φ ⊑ rhs` into the local context via
`le_of_imp_top_le`, leaving `⊤ ⊑ rhs`. Runs after `True` and `⊤` preconditions are handled, so
`φ` carries information worth keeping. Returns the new goal and the introduced hypothesis. -/
private def barePreIntro? (goal : MVarId) (α pre : Expr) : VCGenM (Option (MVarId × FVarId)) := do
  unless α.isProp do return none
  if pre.isAppOf ``Lean.Order.top then return none
  return some (← introPre (← read).backwardRules.propPreIntro goal)

/-- Strategy 7: replace a `True` precondition by `⊤` via `true_le_of_top_le`, or reduce a lifted
`⊤ s₁ … sₙ` precondition (the bare top applied to the state arguments introduced by
`le_of_forall_le`) to the bare `⊤` via a `top_apply` rewrite. Either way the goal follows the `⊤`
path instead of lifting into the local context, and a `⊤`-precondition VC reaches `elimTopPre` in the
bare form that `top_le_prop` can strip. -/
private def normalizePreToTop? (goal : MVarId) (pre target : Expr) : VCGenM (Option (List MVarId)) := do
  if pre.isTrue then
    let .goals [g] ← (← read).backwardRules.truePreIntro.applyChecked goal
      | throwError "Failed to apply {.ofConstName ``Lean.Order.true_le_of_top_le} to{indentExpr target}"
    return some [g]
  if let some g ← reduceTopAppliedPre? goal target pre then
    return some [g]
  return none

/-- Phase 2: drive the precondition of `pre ⊑ rhs` toward `⊤`, lifting any pure content into the
local context so a later spec application sees a `⊤` precondition. In order: cancel a redundant
`⊓ ⊤`; lift an embedded `⌜φ⌝` (before state-argument introduction, which would otherwise leave
`⌜φ⌝` applied to the introduced state); introduce excess state arguments; drop a `True`
precondition; lift a bare `Prop` precondition. Returns the updated scope, recording any lifted
hypothesis. -/
private def normalizePre? (scope : VCGen.Scope) (goal : MVarId) (α pre target : Expr) :
    VCGenM (Option (VCGen.Scope × List MVarId)) := do
  if let some g ← stripMeetTopPre? goal pre then
    return some (scope, [g])
  if let some (g, h) ← ofPropPreIntro? goal pre then
    return some ({ scope with lastLiftedPre? := some h }, [g])
  if let some goal' ← introsExcessArgs goal then return some (scope, [goal'])
  if let some gs ← normalizePreToTop? goal pre target then
    return some (scope, gs)
  if let some (g, h) ← barePreIntro? goal α pre then
    return some ({ scope with lastLiftedPre? := some h }, [g])
  return none

/-- Replace the program in `goal`'s target with `prog` (which must be definitionally equal). -/
private def replaceProgDefEq (goal : MVarId) (info : WPApp) (prog : Expr) :
    VCGenM MVarId := do
  let wp ← mkAppNS info.head <| info.args.set! 7 prog
  let rhs ← mkAppNS wp info.excessArgs
  let target ← goal.getType
  let relArgs := target.getAppArgs
  let newTarget ← mkAppNS target.getAppFn (relArgs.set! (relArgs.size - 1) rhs)
  goal.replaceTargetDefEqFast newTarget

/-- Strip an `mdata` wrapper (such as the `save_info` annotation left by spec elaboration)
from the program in `goal`'s target, so the remaining strategies see the bare term. -/
private def wpConsumeMData? (goal : MVarId) (info : WPApp) : VCGenM (Option MVarId) := do
  let .mdata .. := info.prog | return none
  return some (← replaceProgDefEq goal info info.prog.consumeMData)

/-- `+jp`: wrap the continuation of a `__do_jp` let in `jpGadget`, tagging the join point so the
usual let-introduction runs (`wpLet?`) and `tryJPGadget?` then sets up the shared spec. -/
private def tryMarkJP? (goal : MVarId) (info : WPApp) : VCGenM (Option MVarId) := do
  unless (← read).useJP do return none
  let .letE name ty val body nondep := info.prog.getAppFn | return none
  unless Lean.Elab.Tactic.Do.isJP name do return none
  unless val.isLambda do return none
  if body.getAppFn.isConstOf ``Std.Internal.Do.jpGadget then return none
  let uα ← liftMetaM <| Meta.getLevel info.Prog
  let uβ ← liftMetaM <| Meta.getLevel ty
  let wrapped := Expr.letE name ty val
    (mkAppN (mkConst ``Std.Internal.Do.jpGadget [uα, uβ]) #[info.Prog, ty, .bvar 0, body]) nondep
  return some (← replaceProgDefEq goal info (← mkAppRevS wrapped info.prog.getAppRevArgs))

/-- Strategy 11a: hoist or zeta-substitute a `let` from the program head. -/
private def wpLet? (goal : MVarId) (info : WPApp) : VCGenM (Option MVarId) := do
  let .letE name type val body nondep := info.prog.getAppFn | return none
  let appArgs := info.prog.getAppRevArgs
  if isDuplicable val then
    trace[Elab.Tactic.Do.vcgen] "let-zeta-dup: {name}"
    let body' ← Sym.instantiateRevBetaS body #[val]
    let prog ← mkAppRevS body' appArgs
    return some (← replaceProgDefEq goal info prog)
  else
    trace[Elab.Tactic.Do.vcgen] "let-hoist: {name}"
    let prog ← mkAppRevS body appArgs
    let wp ← mkAppNS info.head <| info.args.set! 7 prog
    let rhs ← mkAppNS wp info.excessArgs
    let target ← goal.getType
    let relArgs := target.getAppArgs
    let target ← mkAppNS target.getAppFn (relArgs.set! (relArgs.size - 1) rhs)
    let target := Expr.letE name type val target nondep
    let goal ← goal.replaceTargetDefEqFast target
    let .goal _ goal ← Sym.intros goal
      | throwError "Failed to intro hoisted let"
    return some goal

/-- Per-alt segment sizes of the alt telescope the body split (`mkBackwardRuleForSplit`, splitter
form with added equalities) introduces at each jump site, computed the same way over the abstracted
split. -/
private def computeBodyAltLayouts (sinfo : Lean.Elab.Tactic.Do.SplitInfo) (progTy : Expr) :
    MetaM (Array (Nat × Nat × Nat × Nat)) := do
  match sinfo with
  | .ite _ | .dite _ => return #[(1, 0, 0, 0), (1, 0, 0, 0)]
  | .matcher _ =>
    let ref ← IO.mkRef (#[] : Array (Nat × Nat × Nat × Nat))
    discard <| sinfo.withAbstract progTy fun abstractInfo _ =>
      abstractInfo.splitWith (mkSort .zero) (useSplitter := true)
          fun _name _expAltType _idx altFVars => do
        ref.modify (·.push (altFVars.fields.size, altFVars.overlaps.size,
          altFVars.discrEqs.size, altFVars.extraEqs.size))
        pure (mkConst ``True)
    ref.get

/-- `+jp`: at `wp⟦jpGadget fv rest⟧` with `rest` an `if`/`match`, register a `Triple` spec for the
join point `fv` and split into two subgoals, the JP body and the (gadget-stripped) `rest`. `body`
is proved once and each jump `fv args` in `rest` closes via `applySpec`.

The spec's precondition splits the same way as `rest`: in branch `i` it is a fresh metavariable
`?Hᵢ`, which the jumps in that branch fill in with the facts that hold there. -/
private def tryJPGadget? (scope : Scope) (goal : MVarId) (info : WPApp) :
    VCGenM (Option SolveResult) := do
  let_expr Std.Internal.Do.jpGadget _α _β fv rest := info.prog | return none
  let some fvId := fv.fvarId? | return none
  goal.withContext do
  -- Strip the gadget for the rest subgoal.
  let restGoal ← replaceProgDefEq goal info rest
  let some sinfo ← liftMetaM <| Lean.Elab.Tactic.Do.getSplitInfo? rest
    | return some (.goalsInScope scope [restGoal])
  let some resTy := sinfo.resTy
    | return some (.goalsInScope scope [restGoal])
  let Q := info.post
  let joinTy ← liftMetaM <| Meta.inferType fv
  let numJoinParams ← liftMetaM <| Lean.Elab.Tactic.Do.getNumJoinParams joinTy resTy

  -- Create the `?Hᵢ` mvars in the outer local context so the rule construction's `abstractMVars`
  -- keeps them shared across jump sites.
  let outerLCtx ← liftMetaM getLCtx
  let outerLocalInsts ← liftMetaM getLocalInstances
  let instCL ← liftMetaM <| Meta.synthInstance (← Meta.mkAppM ``Lean.Order.CompleteLattice #[info.Pred])
  let (bodyTy, hypsMVars, specSizes) ← liftMetaM <|
    Meta.forallBoundedTelescope joinTy numJoinParams fun joinParams _ => do
      let hypsMVarsRef ← IO.mkRef (#[] : Array MVarId)
      let specSizesRef ← IO.mkRef (#[] : Array Nat)
      -- Split the precondition at `Prop` (each `?Hᵢ` produces a `Prop`) and embed the match via `⌜·⌝`.
      -- Each jump discharges its instance by construction (`ofProp_eq_top` of the witnessed alt); the
      -- body proof case-splits the bare `Prop` match that `⌜φ⌝ s` reduces to.
      let propMatch ← sinfo.splitWith (mkSort .zero) (useSplitter := false)
          fun _name _expAltType _idx altFVars => do
        let allBinders := joinParams ++ altFVars.all
        let mvarTy ← Meta.mkForallFVars allBinders (mkSort .zero)
        let hypsMVar ← Meta.mkFreshExprMVarAt outerLCtx outerLocalInsts mvarTy .syntheticOpaque
        hypsMVarsRef.modify (·.push hypsMVar.mvarId!)
        specSizesRef.modify (·.push altFVars.all.size)
        pure (mkAppN hypsMVar allBinders)
      let pjpBody ← Meta.mkAppOptM ``Lean.Order.CompleteLattice.ofProp #[info.Pred, instCL, propMatch]
      let tripleTy ← Meta.mkAppOptM ``Std.Internal.Do.Triple
        #[info.Pred, info.EPred, info.Prog, info.Value, info.args[4]!, info.args[5]!,
          mkAppN fv joinParams, info.instWP, pjpBody, Q, info.args[9]!]
      pure (← Meta.mkForallFVars joinParams tripleTy, ← hypsMVarsRef.get, ← specSizesRef.get)

  let bodySizes ← liftMetaM <| computeBodyAltLayouts sinfo info.Prog
  unless bodySizes.size == specSizes.size do
    throwError "vcgen +jp: alt count mismatch between spec and body splits of{indentExpr rest}"
  let altLayouts := bodySizes.zipWith (fun (bF, bO, bD, bE) sB =>
    { bodyFields := bF, bodyOverlaps := bO, bodyDiscrEqs := bD, bodyExtraEqs := bE
      specBinders := sB : JPAltLayout }) specSizes

  -- `finalizeJPs` assigns each `?Hᵢ` the disjunction of its recorded jump payloads (`False` when
  -- no jump reaches the alt, e.g. behind an early `return` or a `throw`).
  modify fun s => { s with jpHypsMVars := hypsMVars.foldl (·.push ·) s.jpHypsMVars }

  let bodyMV ← liftMetaM <| Meta.mkFreshExprSyntheticOpaqueMVar bodyTy (← goal.getTag)
  -- Bind the body proof as a local hypothesis so each jump references it by fvar (`jpProof joinArgs`),
  -- keeping the shared continuation proof in one `let` binding that survives proof-term instantiation.
  let restGoal ← liftMetaM <| restGoal.define `jpProof bodyTy bodyMV
  let (jpProofFVar, restGoal) ← liftMetaM <| restGoal.intro1P
  let some joinSpec ← liftMetaM <| restGoal.withContext <| SpecAttr.mkSpecTheoremFromLocal jpProofFVar
    | return some (.goalsInScope scope [restGoal])

  let outerLCtxSize := (← restGoal.getDecl).lctx.numIndices
  let jpDefInfo : JPDefInfo := { hypsMVars, splitInfo := sinfo, outerLCtxSize, altLayouts }
  -- `bodyMV` keeps the original scope so its own head is not treated as a JP.
  let restScope := (scope.insertSpec joinSpec).registerJP fvId jpDefInfo
  return some (.goals [(restScope, restGoal), (scope, bodyMV.mvarId!)])

/-- Strategy 11b: split an `ite`/`dite`/match program, or iota-reduce a matcher with a concrete
discriminant. -/
private def wpMatch? (goal : MVarId) (info : WPApp) :
    VCGenM (Option (List MVarId)) := do
  let some splitInfo ← liftMetaM <| Lean.Elab.Tactic.Do.getSplitInfo? info.prog | return none
  if splitInfo matches .matcher .. then
    if let some prog ← liftMetaM <| withReducible <| reduceRecMatcher? info.prog then
      return some [← replaceProgDefEq goal info (← shareCommonInc prog)]
  let rule ← mkBackwardRuleForSplitCached splitInfo info
  let .goals goals ← rule.applyChecked goal m!"split rule for{indentExpr info.prog}"
    | throwError "Failed to apply split rule for {indentExpr info.prog}"
  let mut simpGoals := #[]
  for g in goals do
    match ← simpGoalTelescope g with
    | .goal g' => simpGoals := simpGoals.push g'
    | .noProgress => simpGoals := simpGoals.push g
    | .closed => continue
  return some simpGoals.toList

/-- Strategy 11c: zeta-unfold a let-bound fvar used as the program head, unless it is a registered JP. -/
private def wpFVarZeta? (scope : VCGen.Scope) (goal : MVarId) (info : WPApp) :
    VCGenM (Option MVarId) := do
  let f := info.prog.getAppFn
  let some fvarId := f.fvarId? | return none
  if (scope.knownJP? fvarId).isSome then return none
  let some val ← fvarId.getValue? | return none
  trace[Elab.Tactic.Do.vcgen] "fvar-zeta: {(← fvarId.getUserName)}"
  let prog ← shareCommonInc (val.betaRev info.prog.getAppRevArgs)
  return some (← replaceProgDefEq goal info prog)

/-- Strategy 11d: reduce a projection head in the program. -/
private def wpHeadReduce? (goal : MVarId) (info : WPApp) :
    VCGenM (Option MVarId) := do
  let f := info.prog.getAppFn
  unless f matches .proj .. do return none
  let some f' ← withReducibleAndInstances (reduceProj? f) | return none
  let f' ← shareCommon (← liftMetaM <| unfoldReducible f')
  let prog ← betaRevS f' info.prog.getAppRevArgs
  return some (← replaceProgDefEq goal info prog)

/-- Stop or raise on a program with no matching spec. With `errorOnMissingSpec` (default), raise a
hard error naming the program and any candidate specs; otherwise stop and emit the goal as a VC. -/
private def stopOrErrorOnMissingSpec (prog monad : Expr) (thms : Array SpecTheorem) :
    VCGenM SolveResult := do
  unless (← read).errorOnMissingSpec do
    return .stop (.noSpecFound prog monad thms)
  if thms.isEmpty then
    throwError "No spec found for program {prog}."
  else
    throwError "No spec matching the monad {monad} found for program {prog}. \
      Candidates were {thms.map (·.proof)}."

/-- At a JP jump site `__do_jp args`, build this jump's payload for the applicable alt's
precondition mvar `?Hᵢ`: an existential closure of the join-argument equalities over the jump
site's local context, abstracted over the mvar's binders. Returns `(altIdx, payload, witnesses)`
where `witnesses` are the actual locals for the payload's `∃` binders; `finalizeJPs` assigns
`?Hᵢ` the disjunction of its jumps' payloads and discharges each jump goal by construction. -/
private def mkJPJumpPayload? (jpInfo : JPDefInfo) (e : Expr) :
    VCGenM (Option (Nat × Expr × Array Expr)) := do
  let info := jpInfo.splitInfo
  let joinArgs := e.getAppArgs
  -- The applicable alt is the one whose discriminant `rwIfOrMatcher` succeeds on here.
  let mut altIdx? : Option Nat := none
  for idx in [:info.altInfos.size] do
    let resOpt ← liftMetaM <| try
      some <$> Lean.Elab.Tactic.Do.rwIfOrMatcher idx info.expr
    catch _ => pure none
    let some res := resOpt | continue
    if res.proof?.isNone then continue
    altIdx? := some idx
    break
  let some altIdx := altIdx? | return none
  unless altIdx < jpInfo.hypsMVars.size do return none
  let hypsMVar := jpInfo.hypsMVars[altIdx]!
  trace[Elab.Tactic.Do.vcgen] "JP jump: alt {altIdx} args={joinArgs}"
  let layout := jpInfo.altLayouts[altIdx]!
  liftMetaM do
    let mvarTy ← hypsMVar.getType
    let lctx ← getLCtx
    let newLocalDecls := lctx.decls.foldl (init := #[]) (start := jpInfo.outerLCtxSize) Array.push
      |>.filterMap id
      |>.filter (fun decl => !decl.isImplementationDetail)
    Meta.forallTelescopeReducing mvarTy fun allBinders _ => do
      let numJP := joinArgs.size
      unless numJP ≤ allBinders.size do return none
      let jpBinders := allBinders.extract 0 numJP
      let altBinders := allBinders.extract numJP allBinders.size
      -- The leading jump-site locals are the body split's alt telescope,
      -- `fields ++ overlaps ++ discrEqs ++ extraEqs` with the sizes recorded in `layout`. The mvar's
      -- alt binders are the fields and discrEqs of the spec-side split, so they pair positionally;
      -- the remaining telescope binders are the split's own bookkeeping, which the consuming side
      -- re-derives when it splits the match/ite hypothesis, and are dropped. Locals beyond the
      -- telescope (inner split conditions, monadic binders) are kept and closed over below.
      -- The spec binders are the matcher alt's own parameters, fields first and then discriminant
      -- equations; a thunked nullary alt has a single `Unit` parameter on the spec side only, which
      -- stays unpaired and unused.
      let pairedFields := min layout.specBinders layout.bodyFields
      let pairedEqs := min (layout.specBinders - pairedFields) layout.bodyDiscrEqs
      unless altBinders.size == layout.specBinders &&
          layout.bodyTeleLen ≤ newLocalDecls.size &&
          layout.specBinders - pairedFields - pairedEqs ≤ 1 do
        throwError "vcgen +jp: jump-site telescope does not match the recorded alt layout for \
          {indentExpr e}"
      let mut matchedLocals : Array Expr := #[]
      let mut matchedBinders : Array Expr := #[]
      for i in [:pairedFields] do
        matchedLocals := matchedLocals.push newLocalDecls[i]!.toExpr
        matchedBinders := matchedBinders.push altBinders[i]!
      for i in [:pairedEqs] do
        matchedLocals := matchedLocals.push
          newLocalDecls[layout.bodyFields + layout.bodyOverlaps + i]!.toExpr
        matchedBinders := matchedBinders.push altBinders[pairedFields + i]!
      let eqs ← (jpBinders.mapIdx fun i jp => (jp, i)).mapM fun (jp, i) => Meta.mkEq jp joinArgs[i]!
      let restDecls := newLocalDecls.extract layout.bodyTeleLen newLocalDecls.size
      let restLocals := restDecls.map LocalDecl.toExpr
      -- `∃ rest, joinParams = joinArgs`, existentially/let-closing the kept locals; the paired ones
      -- are then rewritten to the mvar's own alt binders.
      let (_, φPropClosed) ← restDecls.foldrM (init := (restLocals, (mkAndN eqs.toList).abstract restLocals))
          fun decl (locals, φ) => do
        let locals := locals.pop
        let type := (← instantiateMVars decl.type).abstract locals
        match decl.value? with
        | some v =>
          let val := (← instantiateMVars v).abstract locals
          return (locals, Lean.mkLet decl.userName type val φ (nondep := decl.isNondep))
        | none =>
          let typeLevel ← Meta.getLevel decl.type
          return (locals, mkApp2 (mkConst ``Exists [typeLevel]) type (Expr.lam decl.userName type φ .default))
      let φPropClosed := φPropClosed.replaceFVars matchedLocals matchedBinders
      -- The `∃` binders are exactly the non-let rest locals, in order; hand them back as witnesses.
      return some (altIdx, ← Meta.mkLambdaFVars allBinders φPropClosed,
        (restDecls.filter (·.value?.isNone)).map LocalDecl.toExpr)

/-- Prove `∃ locals, ⋀ joinArgs = joinArgs` by supplying each `∃` binder from `witnesses` (the actual
locals) and closing the residual equalities by `rfl`. -/
private partial def fillJPExists (g : MVarId) (witnesses : List Expr) : MetaM Unit := do
  let ty ← Meta.whnfR (← g.getType)
  match_expr ty with
  | Exists α p =>
    let w :: ws := witnesses | throwError "JP witness underflow"
    let hGoal ← Meta.mkFreshExprSyntheticOpaqueMVar (p.beta #[w])
    g.assign (mkApp4 (mkConst ``Exists.intro [← Meta.getLevel α]) α p w hGoal)
    fillJPExists hGoal.mvarId! ws
  | And a b =>
    let ga ← Meta.mkFreshExprSyntheticOpaqueMVar a
    let gb ← Meta.mkFreshExprSyntheticOpaqueMVar b
    g.assign (mkApp4 (mkConst ``And.intro) a b ga gb)
    fillJPExists ga.mvarId! witnesses
    fillJPExists gb.mvarId! witnesses
  | True => g.assign (mkConst ``True.intro)
  | Eq _ lhs _ => g.assign (← Meta.mkEqRefl lhs)
  | _ => throwError "JP witness: unexpected residual{indentExpr ty}"

/-- Close a JP jump's post-monotonicity premise `∀ xs, lhs ⊑ rhs` by reflexivity. Both sides are the
shared continuation the synthetic spec carries as its postcondition, defeq up to the join-point `let`s
and eta, so `rel_refl lhs` is assigned and the kernel discharges the defeq. Left to the worklist, the
target simp would re-verify that continuation at every jump. -/
private def tryCloseTrivialRefl (g : MVarId) : VCGenM Bool :=
  g.withContext do
    forallTelescope (← g.getType) fun xs body => do
      let_expr PartialOrder.rel α inst lhs _rhs := body | return false
      let prf ← mkAppOptM ``Lean.Order.PartialOrder.rel_refl #[α, inst, lhs]
      g.assign (← mkLambdaFVars xs prf)
      return true

/-- Record a JP jump's precondition VC `pre ⊑ ⌜match discrs => ?Hᵢ⌝` for `finalizeJPs`, verifying
that the match reduces to the applicable alt with the jump's discriminant evidence. Returns `true`
when `g` was recorded (and thus withheld from the worklist); other subgoals are left. -/
private def tryDeferJPPrecond (g hypsMVar : MVarId) (altIdx : Nat) (payload : Expr)
    (witnesses : Array Expr) : VCGenM Bool :=
  g.withContext do
    let_expr PartialOrder.rel _l _inst _pre rhs := ← g.getType | return false
    -- `rhs` is `⌜match discrs => ?Hᵢ⌝`, on a stateful assertion applied to the introduced state args.
    let rhsArgs := rhs.getAppArgs
    unless rhs.getAppFn.isConstOf ``CompleteLattice.ofProp && rhsArgs.size ≥ 3 do return false
    let matchExpr := rhsArgs[2]!
    let some red ← liftMetaM <| (try
        some <$> Lean.Elab.Tactic.Do.rwIfOrMatcher altIdx matchExpr
      catch _ => pure none)
      | return false
    let some redProof := red.proof? | return false
    let record : JPJumpRecord :=
      { hypsMVar, goal := g, payload, witnesses, redExpr := red.expr, redProof }
    modify fun s => { s with jpJumps := s.jpJumps.push record }
    return true

/-- Prove disjunct `idx` of the `count`-fold right-nested disjunction `φ`, witnessing the selected
disjunct via `fillJPExists`. -/
private partial def proveJPDisjunct (φ : Expr) (idx count : Nat) (witnesses : List Expr) :
    MetaM Expr := do
  if count == 1 then
    let m ← Meta.mkFreshExprSyntheticOpaqueMVar φ
    fillJPExists m.mvarId! witnesses
    return m
  let_expr Or a b := φ | throwError "JP finalization: expected disjunction{indentExpr φ}"
  match idx with
  | 0 => return mkApp3 (mkConst ``Or.inl) a b (← proveJPDisjunct a 0 1 witnesses)
  | idx + 1 => return mkApp3 (mkConst ``Or.inr) a b (← proveJPDisjunct b idx (count - 1) witnesses)

/-- Discharge a recorded JP jump: prove its own disjunct (number `idx` of `count`) of the assigned
`?Hᵢ`, then close the jump goal `pre ⊑ ⌜match discrs => ?Hᵢ⌝` with it. The state args a stateful
assertion is applied to are stripped with `ofProp_apply` (`⌜φ⌝ s = ⌜φ⌝`) and the proof transported
back to the original goal. -/
private def dischargeJPJump (sctx : Meta.Simp.Context) (r : JPJumpRecord) (idx count : Nat) :
    VCGenM Unit :=
  r.goal.withContext do liftMetaM do
    let_expr PartialOrder.rel _l _inst pre rhs := ← r.goal.getType
      | throwError "JP finalization: unexpected jump goal{indentExpr (← r.goal.getType)}"
    let φPrf ← proveJPDisjunct (← instantiateMVars r.redExpr) idx count r.witnesses.toList
    let hMatch ← Meta.mkEqMP (← Meta.mkEqSymm r.redProof) φPrf
    let leProof ← Meta.mkAppM ``Lean.Order.le_ofProp #[pre, ← Meta.inferType hMatch, hMatch]
    let (res, _) ← Meta.simp rhs sctx
    match res.proof? with
    | some rhsEq =>
      let motive ← Meta.withLocalDeclD `x (← Meta.inferType rhs) fun x => do
        Meta.mkLambdaFVars #[x] (← Meta.mkAppM ``PartialOrder.rel #[pre, x])
      r.goal.assign (← Meta.mkEqMPR (← Meta.mkCongrArg motive rhsEq) leProof)
    | none => r.goal.assign leProof

/-- Assign every `+jp` alt-precondition mvar `?Hᵢ` the disjunction of the payloads its recorded
jumps provided (`False` when no jump reaches the alt, e.g. behind an early `return` or a `throw`),
then discharge each recorded jump goal with its own disjunct. -/
public def finalizeJPs : VCGenM Unit := do
  let s ← get
  if s.jpHypsMVars.isEmpty then return
  let sthms ← ({} : Meta.SimpTheorems).addConst ``Lean.Order.CompleteLattice.ofProp_apply
  let sctx ← Meta.Simp.mkContext (simpTheorems := #[sthms])
  let grouped : Std.HashMap MVarId (Array JPJumpRecord) :=
    s.jpJumps.foldl (init := {}) fun m r =>
      m.alter r.hypsMVar (fun rs? => some ((rs?.getD #[]).push r))
  for mv in s.jpHypsMVars do
    let records := grouped.getD mv #[]
    unless ← mv.isAssigned do
      liftMetaM <| Meta.forallTelescopeReducing (← mv.getType) fun bs _ => do
        let props := records.map (·.payload.beta bs)
        let φ := match props.back? with
          | none => mkConst ``False
          | some last => props.pop.foldr (init := last) mkOr
        mv.assign (← Meta.mkLambdaFVars bs φ)
    for h : i in [:records.size] do
      dischargeJPJump sctx records[i] i records.size

/-- Select the highest-priority `@[spec]` theorem matching `prog`, or a stop result when none matches.
Hands `findSpecs` the sole reference to the spec database so its in-place pattern internalization does
not copy the discrimination tree, then threads the updated database back into the returned scope. -/
private def findSpec (scope : VCGen.Scope) (prog monad : Expr) :
    VCGenM (VCGen.Scope × Except SolveResult SpecTheorem) := do
  let specs := scope.specs
  let scope := { scope with specs := default }
  let (result, specs) ← SpecTheorems.findSpecs specs prog
  let scope := { scope with specs }
  match result with
  | .ok thm => return (scope, .ok thm)
  | .error thms => return (scope, .error (← stopOrErrorOnMissingSpec prog monad thms))

/-- True iff the spec's pattern unifies with the program, mirroring the match performed in
`findSpecs`. Distinguishes a spurious discrimination-tree candidate, whose pattern does not unify,
from a spec whose pattern matches yet whose backward rule fails to apply. -/
private def specPatternMatches (thm : SpecTheorem) (prog : Expr) : SymM Bool :=
  withNewMCtxDepth do
    return (← thm.pattern.match? prog).isSome

/-- Apply the cached backward rule of the selected `@[spec]` theorem `thm`, returning its subgoals, or
a stop result when no rule matches the goal's monad. Reached from `applyFrameOrSpec`. -/
private def applySpec (scope : VCGen.Scope) (goal : MVarId) (info : WPApp) (thm : SpecTheorem) :
    VCGenM SolveResult := do
  trace[Elab.Tactic.Do.vcgen] "Applying spec {thm.proof} for {info.prog}. Excess args: {info.excessArgs}"
  -- At a JP jump site, build its alt-precondition payload, then build the rule at a fresh mvar depth
  -- so the synthetic body/precondition mvars survive `abstractMVars` as constants (shared across jump
  -- sites).
  let jpInfo? := info.prog.getAppFn.fvarId?.bind scope.knownJP?
  let jpJump? ← match jpInfo? with
    | some jpInfo => mkJPJumpPayload? jpInfo info.prog
    | none => pure none
  let some rule ←
    try
      let build := (mkBackwardRuleFromSpecCached thm info).run
      if jpInfo?.isSome then Meta.withNewMCtxDepth (allowLevelAssignments := false) build else build
    catch ex =>
      throwError "Failed to construct rule {thm.proof} for {indentExpr info.prog}\n\
        error: {ex.toMessageData}\n\
        target:{indentExpr (← goal.getType)}\n\
        Pred:{indentExpr info.Pred}\n\
        excessArgs: {info.excessArgs}"
    | return ← stopOrErrorOnMissingSpec info.prog info.M #[thm]
  let .goals goals ← rule.applyChecked goal m!"spec rule for{indentExpr info.prog}"
    | do
      -- The discrimination tree over-approximates, so a selected spec may not unify with the program
      -- (e.g. an offset-keyed equation against a variable discriminant). That is no matching spec, not
      -- a rule failure. A spec whose pattern does match yet whose rule fails to apply is a genuine bug.
      unless ← specPatternMatches thm info.prog do
        return ← stopOrErrorOnMissingSpec info.prog info.M #[thm]
      let ruleType ← Meta.inferType rule.expr
      throwError "Failed to apply rule {thm.proof} for {indentExpr info.prog}\n\
        target:{indentExpr (← goal.getType)}\n\
        Pred:{indentExpr info.Pred}\n\
        excessArgs: {info.excessArgs}\n\
        rule type:{indentExpr ruleType}"
  if let some (altIdx, payload, witnesses) := jpJump? then
    let hypsMVar := (jpInfo?.get!).hypsMVars[altIdx]!
    let mut remaining := #[]
    let mut deferred := false
    for g in goals do
      if ← tryDeferJPPrecond g hypsMVar altIdx payload witnesses then
        deferred := true
      else if ← tryCloseTrivialRefl g then
        pure ()
      else
        remaining := remaining.push g
    unless deferred do
      throwError "vcgen +jp: jump {indentExpr info.prog}\nyielded no precondition subgoal to defer"
    return .goalsInScope scope remaining.toList
  return .goalsInScope scope goals

/-- True iff the program matches the `until` pattern, in which case VC generation stops at this
goal. -/
private def matchesUntilPattern (prog : Expr) : VCGenM Bool := do
  let some pat := (← read).untilPat? | return false
  if (← pat.match? prog).isSome then
    trace[Elab.Tactic.Do.vcgen] "`until` pattern matched program {prog}; stopping"
    return true
  return false

/-- `let`-declaration analogue of `withLocalDeclsDND`: brings each `name : type := value` into scope
(types and values mutually independent), then runs `k` with the new free variables. -/
@[inline]
private def withLetDeclsDND (declInfos : Array (Name × Expr × Expr))
    (k : Array Expr → VCGenM Expr) : VCGenM Expr :=
  loop #[]
where
  loop (acc : Array Expr) : VCGenM Expr := do
    if h : acc.size < declInfos.size then
      let (name, type, value) := declInfos[acc.size]
      Meta.withLetDecl name type value fun fv => loop (acc.push fv)
    else
      k acc
  termination_by declInfos.size - acc.size

/-- Elaborate a matched `frames` alternative's frame term at the resource type `resourceTy` of the
applicable frame operator, with each named pattern variable bound to the subterm the pattern matched.
The bindings are introduced as `let`-declarations carrying the matched value, so the resulting frame
records the pattern-variable assignments and the user sees them in the side goals. -/
private def elabFrame (resourceTy : Expr) (entry : FrameEntry) (res : Sym.MatchUnifyResult) :
    VCGenM Expr := do
  let mut decls : Array (Name × Expr × Expr) := #[]
  for h : i in [0:entry.varNames.size] do
    if let some nm := entry.varNames[i] then
      if h2 : i < res.args.size then
        decls := decls.push (nm, ← Meta.inferType res.args[i]!, res.args[i]!)
  Meta.withDefault <| withLetDeclsDND decls fun fvs => do
    let frameExpr ← Lean.Elab.Term.TermElabM.run' do
      let e ← Lean.Elab.Term.elabTermEnsuringType entry.frameStx (some resourceTy)
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      mkLetFVars fvs e
    instantiateMVarsS frameExpr

/-- Find an unretired `frames` alternative matching the program (earliest source order wins),
elaborate its frame at the resource type `resourceTy`, and retire it so it applies at most once. -/
public def matchFrame? (resourceTy : Expr) (info : WPApp) : VCGenM (Option Expr) := do
  let db := (← get).frameDB
  let mut best : Option (FrameEntry × Sym.MatchUnifyResult) := none
  for srcIdx in Sym.getMatch db.tree info.prog do
    let entry := db.entries[srcIdx]!
    if entry.retired then continue
    if let some res ← entry.pat.match? info.prog then
      match best with
      | none => best := some (entry, res)
      | some (b, _) => if entry.srcIdx < b.srcIdx then best := some (entry, res)
  let some (entry, res) := best | return none
  modify fun s =>
    let entries := s.frameDB.entries.set! entry.srcIdx { entry with retired := true }
    { s with frameDB := { s.frameDB with entries } }
  let F ← elabFrame resourceTy entry res
  trace[Elab.Tactic.Do.vcgen] "`frames` matched {info.prog}; frame:{indentExpr F}"
  return some F

/-- True iff `post` is the post of a frame residual, `fun a => PreservesSup.upperAdjoint (op F) (Q a)`.
The upper-adjoint frame rule leaves this shape behind, so a program with such a post is already framed
and must not be framed again. -/
private def isFramedPost (post : Expr) : Bool :=
  let body := if post.isLambda then post.bindingBody! else post
  body.consumeMData.getAppFn.isConstOf ``Lean.Order.PreservesSup.upperAdjoint

/-- Apply the upper-adjoint frame rule for `fp`'s operator and frame `F`, assigning the schematic frame
variable to `F`. Returns the frame VCs, the frame condition `WP.Frames op prog F`, and the
precondition that carries on to the program's own spec. Builds the operator here, since this runs only
when a frame applies. -/
private def applyFrameRule (goal : MVarId) (info : WPApp) (fp : FrameProc) (F : Expr) :
    VCGenM (List MVarId) := do
  let op ← fp.mkOpAppM info
  let rule ← mkFrameBackwardRuleCached op info
  let .goals (fGoal :: rest) ← rule.applyChecked goal m!"frame rule for{indentExpr info.prog}"
    | throwError "frame: failed to apply rule for{indentExpr info.prog}"
  -- `fGoal` is the schematic frame variable, of the operator's resource type `R`; `F` was inferred at
  -- that same `R`, so it assigns directly without a definitional-equality check.
  fGoal.assign F
  return rest

/-- The spec precondition instantiated at the call site: the right-hand side of the bare `pre ⊑ specPre`
premise among a spec rule's subgoals. The post and exception VCs are `∀`-quantified, so the bare
entailment is the precondition VC. -/
private def specPreOf? (subgoals : List MVarId) : VCGenM (Option Expr) := do
  for g in subgoals do
    if let some (_, _, _, specPre) := (← g.getType).app4? ``Lean.Order.PartialOrder.rel then
      -- Resolve only an assigned head mvar so the procedure's head test (`isAppOf`) sees the real
      -- operator; nested mvars are resolved by the procedure's own unification.
      return some (← instantiateMVarsIfMVarAppS specPre)
  return none

/--
Handle a spec-ready program `info.prog`: select its `@[spec]` theorem and either frame or apply it.

- A spec with a conjunctive precondition, or an already-framed residual, applies its spec directly.
- Otherwise the frame operator for the monad is selected (the `@[frameproc]` registered for the
  program type, or the default meet frame). The choice is per node, since sub-programs may reach a
  different monad (e.g. a `monadLift`ed base call).
- An explicit `frames` clause takes precedence, framing eagerly.
- Failing that, the spec is applied speculatively and its precondition VC `pre ⊑ specPre` is handed to
  the frame procedure: no frame keeps the application; a frame `F` rolls it back and applies the frame
  rule instead, so the spec re-applies against the framed residual where its VCs are solvable.
-/
private def applyFrameOrSpec (scope : VCGen.Scope) (goal : MVarId) (pre : Expr) (info : WPApp) :
    VCGenM SolveResult := goal.withContext do
  let (scope, spec) ← findSpec scope info.prog info.M
  let thm ← match spec with
    | .ok thm => pure thm
    | .error res => return res
  -- A JP jump site applies its synthetic spec directly, bypassing framing.
  let isJP := (info.prog.getAppFn.fvarId?.bind scope.knownJP?).isSome
  if thm.conjunctivePre || isFramedPost info.post || isJP then
    return ← applySpec scope goal info thm
  let procs := (← read).frameProcs.byProg
  let fp := info.M.getAppFn.constName?.bind (procs[·]?) |>.getD meetFrameProc
  let resourceTy ← fp.resourceTy info
  if let some F ← matchFrame? resourceTy info then
    return .goalsInScope scope (← applyFrameRule goal info fp F)
  let some proc := fp.proc | return ← applySpec scope goal info thm
  -- Apply the spec speculatively, then let the frame procedure inspect its precondition VC. No frame
  -- keeps the application; a frame rolls it back and frames instead.
  let saved ← Meta.saveState
  let .goals scopedSubgoals ← applySpec scope goal info thm
    | throwError "vcgen: speculative spec application for{indentExpr info.prog} did not produce goals"
  let subgoals := scopedSubgoals.map Prod.snd
  let frame? ← match ← specPreOf? subgoals with
    | some specPre => proc resourceTy pre info specPre
    | none => pure none
  let some F := frame? | return .goals scopedSubgoals
  -- Capture the frame before rolling back: `saved.restore` un-assigns the speculative metavariables,
  -- so instantiate `F` against them now (and reshare).
  let F ← instantiateMVarsS F
  trace[Elab.Tactic.Do.vcgen] "`@[frameproc]` matched {info.prog}; frame:{indentExpr F}"
  saved.restore
  return .goalsInScope scope (← applyFrameRule goal info fp F)

/--
The main VC generation step. Operates on a plain `MVarId` with no knowledge of grind.
Returns `.goals subgoals` when the goal was decomposed, or a classification result
(`.noEntailment`, `.noProgramOrLatticeFoundInTarget`, etc.) when no further decomposition is
possible.

The function performs the following steps in order:

1. **Forall introduction**: If the target is a `∀`, simp it and introduce binders.
2. **Target-let handling**: zeta-substitute duplicable top-level lets, otherwise introduce them.
3. **Triple unfolding**: If the target is `⦃P⦄ x ⦃Q; E⦄`, unfold into `P ⊑ wp x Q E`.
4. **Syntactic rfl**: close `pre ⊑ rhs` by `PartialOrder.rel_refl` when both sides unify.
5. **Embedded pure precondition introduction**: lift a `⌜φ⌝` precondition into the local
   context, before state-argument introduction would apply it to the introduced arguments.
6. **State-argument introduction**: If the lattice carrier is a function type
   `σ₁ → ... → σₙ → Base`, introduce all excess state arguments.
7. **Bare pure precondition introduction**: on the `Prop` lattice, replace a `True`
   precondition by `⊤` and lift any other precondition into the local context.
8. **EPost projection reduction**: reduce an `EPost.Cons.head` RHS to the projected component.
9. **Lattice decomposition**: decompose `⊓`, `⇨`, `⌜p⌝` and `⊤` RHS connectives.
10. **Lifted-hypothesis discharge**: close a residual `pre ⊑ ⌜φ⌝` entailment against the most
    recently lifted precondition `h : φ` in the local context, cached in `Scope.lastLiftedPre?`.
11. **WP decomposition**: when the RHS is `wp e post epost s₁ ... sₙ`, in order:
    hoist/zeta program-head lets, split `ite`/`dite`/match, zeta-unfold fvar program heads,
    reduce projection heads, and finally apply a registered `@[spec]` theorem.
-/
public def solve (scope : VCGen.Scope) (goal : MVarId) : VCGenM SolveResult := goal.withContext do
  if ← outOfFuel then return .stop .outOfFuel
  let target ← goal.getType
  trace[Elab.Tactic.Do.vcgen] "🎯 Target: {target}"

  -- Phase 1: simplify `target` until it is of the form `pre ⊑ rhs`.
  if let some g ← consumeMData? goal target then return .goalsInScope scope [g]
  if let some gs ← forallIntro? goal target then return .goalsInScope scope gs
  if let some g ← targetLetIntro? goal target then return .goalsInScope scope [g]
  if let some g ← tripleUnfold? goal target then return .goalsInScope scope [g]
  if let some g ← bareWPToLe? goal target then return .goalsInScope scope [g]
  if let some gs ← liftedHypBare? scope goal target then return .goalsInScope scope gs

  let_expr PartialOrder.rel α inst pre rhs := target
    | return .stop (.noEntailment target)

  -- A previous rule application may have assigned the entailment's sides to fresh metavariables
  -- (e.g. a lattice-split operand). Instantiate those heads so the shape tests below see the
  -- assigned form.
  let pre ← instantiateMVarsIfMVarAppS pre
  let rhs ← instantiateMVarsIfMVarAppS rhs

  -- Phase 2: close reflexive goals, then drive `pre` toward `⊤`, lifting any pure content so a
  -- later spec application sees a `⊤` precondition.
  if let some gs ← rfl? goal then return .goalsInScope scope gs
  if let some (scope, gs) ← normalizePre? scope goal α pre target then return .goalsInScope scope gs

  -- Collect new local specs before any strategy that may emit multiple subgoals
  -- (`wpMatch?`, `splitLatticeOp?`) or apply a registered spec (`applySpec`).
  let scope ← scope.collectLocalSpecs goal

  -- Phase 3: shape the `rhs` (reduce an EPost projection, decompose a lattice connective or a
  -- forall, then discharge a residual entailment against the lifted hypothesis).
  if let some g ← reduceEPostHead? goal target α inst pre rhs then return .goalsInScope scope [g]
  if let some gs ← splitLatticeOp? goal rhs then return .goalsInScope scope gs
  if let some gs ← splitForallLe? goal rhs then return .goalsInScope scope gs
  if let some gs ← liftedHyp? scope goal α pre rhs then return .goalsInScope scope gs

  -- Phase 4: wp decomposition. The program-shape steps below all consume one unit of fuel
  -- (the `stepLimit` config option) when they make progress.
  if let some info := isWPApp? rhs then
    trace[Elab.Tactic.Do.vcgen] "📜 Program: {info.prog}"
    -- Stop if the program matches the `until` pattern.
    if ← matchesUntilPattern info.prog then
      return .stop (.untilPatternMatched info.M)
    if let some g ← wpConsumeMData? goal info then
      return .goalsInScope scope [g]
    if let some r ← tryJPGadget? scope goal info then
      VCGen.burnOne
      return r
    if let some g ← tryMarkJP? goal info then
      return .goalsInScope scope [g]
    if let some g ← wpLet? goal info then
      VCGen.burnOne
      return .goalsInScope scope [g]
    if let some gs ← wpMatch? goal info then
      VCGen.burnOne
      return .goalsInScope scope gs
    if let some g ← wpFVarZeta? scope goal info then
      VCGen.burnOne
      return .goalsInScope scope [g]
    if let some g ← wpHeadReduce? goal info then
      VCGen.burnOne
      return .goalsInScope scope [g]
    let f := info.prog.getAppFn
    if f.isConst || f.isFVar then
      VCGen.burnOne
      return ← applyFrameOrSpec scope goal pre info
    throwError "Failed to decompose weakest precondition for {info.prog}. This should not happen."

  return .stop (.noProgress pre rhs)

end VCGen

end Lean.Elab.Tactic.Do.Internal
