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
  /-- Successfully decomposed the goal. These are the subgoals, sharing `scope`. -/
  | goals (scope : VCGen.Scope) (subgoals : List MVarId)
  /-- No further progress possible; emit the current goal as a VC. -/
  | stop (reason : SolveResult.StopReason)

private def isDuplicable (e : Expr) : Bool := match e with
  | .bvar .. | .mvar .. | .fvar .. | .const .. | .lit .. | .sort .. => true
  | .mdata _ e | .proj _ _ e => isDuplicable e
  | .lam .. | .forallE .. | .letE .. => false
  | .app .. => e.isAppOf ``OfNat.ofNat

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

private def throwIfUnsupportedJP (name : Name) (val : Expr) : VCGenM Unit := do
  if (← read).useJP && Lean.Elab.Tactic.Do.isJP name && val.isLambda then
    throwError "vcgen: shared-continuation handling for `__do_jp` is not yet \
      implemented. Detection point reached at {name}; the upstream \
      `Lean.Elab.Tactic.Do.onJoinPoint` (`src/Lean/Elab/Tactic/Do/VCGen.lean:215`) \
      needs to be ported to the worklist style. Drop `(jp := true)` to fall back \
      to the default zeta-unfold behaviour."

/-- Strategy 2: zeta-substitute a duplicable top-level `let` in the target, otherwise
introduce it into the local context. -/
private def targetLetIntro? (goal : MVarId) (target : Expr) : VCGenM (Option MVarId) := do
  let .letE name _ val body _ := target | return none
  throwIfUnsupportedJP name val
  if isDuplicable val then
    trace[Elab.Tactic.Do.vcgen] "let-zeta-dup: {name}"
    return some (← goal.replaceTargetDefEq (← Sym.instantiateRevBetaS body #[val]))
  else
    trace[Elab.Tactic.Do.vcgen] "let-intro: {name}"
    return some (← introsHygienic goal)

/-- Strategy 3: unfold a `Triple` target into the underlying lattice entailment. -/
private def tripleUnfold? (goal : MVarId) (target : Expr) : VCGenM (Option MVarId) := do
  unless target.isAppOf ``Triple do return none
  return some (← unfoldTriple goal)

/-- Extract the weakest-precondition metadata from the RHS of a lattice entailment. -/
private def getWPInfo? (rhs : Expr) : Option WPInfo :=
  rhs.withApp fun head args =>
    if head.isConstOf ``Std.Internal.Do.wp && args.size ≥ 10 then
      some { head, args := args.take 10, excessArgs := args.drop 10 }
    else
      none

/-- Strategy 3b: turn a bare `wp` application target (a `Prop`) into `⊤ ⊑ wp …`. Entry-point
goals produced by the `of_wp_run_eq` lemmas have this shape. -/
private def bareWPToLe? (goal : MVarId) (target : Expr) : VCGenM (Option MVarId) := do
  let some _ := getWPInfo? target | return none
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
  let .goals gs ← (← read).backwardRules.refl.apply goal | return none
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
private def replaceProgDefEq (goal : MVarId) (info : WPInfo) (prog : Expr) :
    VCGenM MVarId := do
  let wp ← mkAppNS info.head <| info.args.set! 7 prog
  let rhs ← mkAppNS wp info.excessArgs
  let target ← goal.getType
  let relArgs := target.getAppArgs
  let newTarget ← mkAppNS target.getAppFn (relArgs.set! (relArgs.size - 1) rhs)
  goal.replaceTargetDefEq newTarget

/-- Strategy 11a: hoist or zeta-substitute a `let` from the program head. -/
private def wpLet? (goal : MVarId) (info : WPInfo) : VCGenM (Option MVarId) := do
  let .letE name type val body nondep := info.prog.getAppFn | return none
  let appArgs := info.prog.getAppRevArgs
  throwIfUnsupportedJP name val
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
    let goal ← goal.replaceTargetDefEq target
    let .goal _ goal ← Sym.intros goal
      | throwError "Failed to intro hoisted let"
    return some goal

/-- Strategy 11b: split an `ite`/`dite`/match program, or iota-reduce a matcher with a concrete
discriminant. -/
private def wpMatch? (goal : MVarId) (info : WPInfo) :
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

/-- Strategy 11c: zeta-unfold a local let-bound fvar used as the program head. -/
private def wpFVarZeta? (goal : MVarId) (info : WPInfo) :
    VCGenM (Option MVarId) := do
  let f := info.prog.getAppFn
  let some fvarId := f.fvarId? | return none
  let some val ← fvarId.getValue? | return none
  trace[Elab.Tactic.Do.vcgen] "fvar-zeta: {(← fvarId.getUserName)}"
  let prog ← shareCommonInc (val.betaRev info.prog.getAppRevArgs)
  return some (← replaceProgDefEq goal info prog)

/-- Strategy 11d: reduce a projection head in the program. -/
private def wpHeadReduce? (goal : MVarId) (info : WPInfo) :
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

/-- Strategy 11e: look up a registered `@[spec]` theorem (triple or simp) for the program head
and apply its cached backward rule. -/
private def applySpec (scope : VCGen.Scope) (goal : MVarId) (info : WPInfo) :
    VCGenM SolveResult := do
  trace[Elab.Tactic.Do.vcgen] "Applying a spec for {info.prog}. Excess args: {info.excessArgs}"
  -- Hand `findSpecs` the sole reference to the database so its in-place pattern internalization
  -- does not copy the discrimination tree, then thread the updated database back into the scope.
  let specs := scope.specs
  let scope := { scope with specs := default }
  let (result, specs) ← SpecTheorems.findSpecs specs info.prog
  let scope := { scope with specs }
  match result with
  | .error thms => stopOrErrorOnMissingSpec info.prog info.m thms
  | .ok thm =>
  trace[Elab.Tactic.Do.vcgen] "Spec for {info.prog}: {thm.proof}"
  let some rule ←
    try
      mkBackwardRuleFromSpecCached thm info |>.run
    catch ex =>
      throwError "Failed to construct rule {thm.proof} for {indentExpr info.prog}\n\
        error: {ex.toMessageData}\n\
        target:{indentExpr (← goal.getType)}\n\
        Pred:{indentExpr info.Pred}\n\
        excessArgs: {info.excessArgs}"
    | stopOrErrorOnMissingSpec info.prog info.m #[thm]
  let .goals goals ← rule.applyChecked goal m!"spec rule for{indentExpr info.prog}"
    | do
      let ruleType ← Meta.inferType rule.expr
      throwError "Failed to apply rule {thm.proof} for {indentExpr info.prog}\n\
        target:{indentExpr (← goal.getType)}\n\
        Pred:{indentExpr info.Pred}\n\
        excessArgs: {info.excessArgs}\n\
        rule type:{indentExpr ruleType}"
  return .goals scope goals

/-- True iff the program matches the `until` pattern (elaborated lazily against the program
monad), in which case VC generation stops at this goal. -/
private def matchesUntilPattern (m prog : Expr) : VCGenM Bool := do
  let some ref := (← read).untilPat? | return false
  let pat ← (← ref.get).force ref.set m
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
      instantiateMVars e
    mkLetFVars fvs frameExpr

/-- Find an unretired `frames` alternative matching the program (earliest source order wins),
elaborate its frame at the resource type `resourceTy`, and retire it so it applies at most once. The
frame DB is materialized into `State` on first use. -/
public def matchFrame? : VCGen.FrameInferenceProc := fun resourceTy _pre info => do
  let db ← (← get).frameDB.force (fun d => modify fun s => { s with frameDB := d }) info.m
  let mut best : Option (FrameEntry × Sym.MatchUnifyResult) := none
  for srcIdx in Sym.getMatch db.tree info.prog do
    let entry := db.entries[srcIdx]!
    if entry.retired then continue
    if let some res ← entry.pat.match? info.prog then
      match best with
      | none => best := some (entry, res)
      | some (b, _) => if entry.srcIdx < b.srcIdx then best := some (entry, res)
  let some (entry, res) := best | return none
  modify fun s => { s with frameDB := s.frameDB.modifyElaborated fun db =>
    { db with entries := db.entries.set! entry.srcIdx { entry with retired := true } } }
  let F ← elabFrame resourceTy entry res
  trace[Elab.Tactic.Do.vcgen] "`frames` matched {info.prog}; frame:{indentExpr F}"
  return some F

/-- The outcome of the frame dispatcher `applyFrame`. -/
inductive FrameResult where
  /-- A `frames` alternative matched `info.prog` and was applied; these are its subgoals. -/
  | framed (scope : VCGen.Scope) (subgoals : List MVarId)
  /-- No frame applies: either no alternative matched, or a `skipFrame` marker was stripped.
  The caller applies the program's own spec to `goal` with the (possibly updated) `info`. -/
  | notFramed (goal : MVarId) (info : WPInfo)

/-- Find a frame `F` for `info.prog` together with its frame operator `op : R → Pred → Pred`. The
operator is the one of the `@[frameproc]` registered for the program's type (the monad), or the
lattice meet (resource type `R = Pred`) if none is registered. The frame `F : R` is taken from an
explicit `frames` clause first (elaborated at the operator's resource type), then from the registered
procedure. -/
private def matchFrameProc? (pre : Expr) (info : WPInfo) :
    VCGenM (Option (Expr × Expr)) := do
  let procs ← getFrameProcs
  let fp? := (info.m.getAppFn.constName?).bind (procs.procs[·]?)
  let (op, resourceTy) ← match fp? with
    | some fp =>
      let op ← fp.op info
      pure (op, (← Meta.inferType op).bindingDomain!)
    | none =>
      let op ← Meta.mkAppOptM ``Lean.Order.meet #[info.Pred, none]
      pure (op, info.Pred)
  if let some F ← (← read).frameInferenceProc.toProc resourceTy pre info then
    return some (F, op)
  let some fp := fp? | return none
  let some F ← fp.proc resourceTy pre info | return none
  trace[Elab.Tactic.Do.vcgen] "`@[frameproc]` matched {info.prog}; frame:{indentExpr F}"
  return some (F, op)

/--
Frame dispatcher for a spec-ready program `info.prog`:
* If the program is `skipFrame x` (an already-framed program), strip the marker and
  report `.notFramed`, so framing happens at most once per occurrence.
* If no frame applies, report `.notFramed`.
* Otherwise, apply the frame gadget for the inferred operator `op` and frame `F` as an artificial
  per-call spec. The precondition `op F (wp (skipFrame prog) (op F -* Q))` splits into the frame VC
  `· ⊑ F` and the `skipFrame`-marked frame-enhanced program, and the frame condition VC
  `Frames op prog F` becomes another VC, reported as `.framed`. The lattice meet keeps the precise
  meet gadget; any other residuated operator uses the general gadget with the operator pinned.
-/
private def applyFrame (scope : VCGen.Scope) (goal : MVarId) (pre : Expr) (info : WPInfo) :
    VCGenM FrameResult := goal.withContext do
  if info.prog.getAppFn.isConstOf ``Std.Internal.Do.Gadget.skipFrame then
    let strippedProg := info.prog.appArg!
    let goal ← replaceProgDefEq goal info strippedProg
    return .notFramed goal { info with args := info.args.set! 7 strippedProg }
  -- Do not frame the monad's structural combinators: let them decompose through their specs first,
  -- so frame inference applies to the leaf calls rather than to a `bind`/`map`/`seq` node.
  if let some head := info.prog.getAppFn.constName? then
    if [``Bind.bind, ``Pure.pure, ``Functor.map, ``Seq.seq, ``SeqRight.seqRight,
        ``SeqLeft.seqLeft].contains head then
      return .notFramed goal info
  let some (F, op) ← matchFrameProc? pre info
    | return .notFramed goal info
  -- `info.args.take 7` are the program's own `wp` arguments (program type, value, assertions, `WP`
  -- instance); `mkAppOptM` synthesizes the remaining instances against the assertion's own
  -- `CompleteLattice` so the framing shares the structure the program's `wp` uses. The lattice meet
  -- is just the instance `op := (· ⊓ ·)`; its residual folds to `⇨` (see `foldUpperAdjointMeet?`).
  let specProof ←
    Meta.mkAppOptM ``Std.Internal.Do.Gadget.op_wp_upperAdjoint_le_wp_skipFrame
      ((info.args.take 7).map some ++ #[none, some op, none, some F])
  let some specThm ← mkSpecTheoremFromStx (← getRef) specProof
    | throwError "frame: could not build spec from the frame gadget for{indentExpr info.prog}"
  let some rule ← (tryMkBackwardRuleFromSpec specThm info).run
    | throwError "frame: failed to build rule for{indentExpr info.prog}"
  let .goals subgoals ← rule.applyChecked goal m!"frame rule for{indentExpr info.prog}"
    | throwError "frame: failed to apply rule for{indentExpr info.prog}"
  return .framed scope subgoals

/-- Fold a frame residual `upperAdjoint (meet F) b` on the RHS to Heyting `F ⇨ b` (definitionally
equal: `himp` *is* the meet upper adjoint), exposing the meet operand `F` so the `himp` split can
decompose it. This lets the lattice meet be framed by the general gadget like any operator, with no
meet-specific spec; a non-meet operator's residual is left for its registered `impSplit`. -/
private def foldUpperAdjointMeet? (goal : MVarId) (target rhs : Expr) : VCGenM (Option MVarId) := do
  unless rhs.isAppOf ``Lean.Order.PreservesSup.upperAdjoint do return none
  let args := rhs.getAppArgs
  let some slice := args[2]? | return none
  unless slice.isAppOf ``Lean.Order.meet && slice.getAppNumArgs == 3 do return none
  let himpExpr ← Meta.mkAppM ``Lean.Order.himp #[slice.appArg!, args[3]!]
  let newRhs ← mkAppNS himpExpr (args.extract 4 args.size)
  let relArgs := target.getAppArgs
  let newTarget ← mkAppNS target.getAppFn (relArgs.set! (relArgs.size - 1) newRhs)
  return some (← goal.replaceTargetDefEq newTarget)

/-- `unfoldReducible`-normalize a goal's target, so a later `applyChecked` unifies past reducible state
types (`StateM σ`, `Tick`, …) that sit behind reducible definitions — the normalization that
`BackwardRule.applyChecked`'s `+debug` retry (`Util.lean`) diagnoses. When `betaRhs` is set, the RHS of
the `pre ⊑ rhs` target is also beta-reduced first (the wand reduction leaves a `(fun m => …) s` redex
whose inner `wp` head must be exposed). -/
private def normalizeReducedGoal (goal : MVarId) (betaRhs : Bool := false) : VCGenM MVarId := do
  let ty ← goal.getType
  unless betaRhs do return ← goal.replaceTargetDefEq (← unfoldReducible ty)
  let relArgs := ty.getAppArgs
  let some rhs := relArgs[relArgs.size - 1]? | return goal
  let newTarget ← mkAppNS ty.getAppFn (relArgs.set! (relArgs.size - 1) (← unfoldReducible rhs.headBeta))
  goal.replaceTargetDefEq newTarget

/-- Fallback for a registered frame `conj` that the direct `splitLatticeOp?` could not peel over a
*nested-base* assertion lattice: `vcgen` introduced an extra inner state coordinate, so the goal is
`conj c R n s` — one application deeper than the registered direct split lemma expects — and
`splitLatticeOp?` returns `none`.

Build a backward rule from the registered `conjReduce` equation (`conj c R = <built-in connective>`,
e.g. a `meet`) via `mkReduceRule` and `applyChecked` it. The rule's conclusion has the same head as the
goal, so it unifies directly (no defeq/normalization); its single premise `pre ⊑ <connective> n s` is the
reduced subgoal. `unfoldReducible`-normalize it so the next iteration's `splitLatticeOp?` decomposes the
exposed connective over *all* coordinates and the operand `wp` flows into the normal spec step.

Keyed on `customConjReduces`, so only registered frame `conj` heads are touched, and run *after* the
direct split and the wp phase — a flat lattice keeps its direct split, and only the nested case that
would otherwise stall on `.noProgress` reaches here. Terminates: each firing exposes a non-`conj`
connective head, so it never re-fires on its own output. -/
private def reduceFrameConj? (goal : MVarId) (rhs : Expr) : VCGenM (Option MVarId) := do
  let some headName := rhs.getAppFn.constName? | return none
  let some eqName := (← read).customConjReduces[headName]? | return none
  let some rule ← mkReduceRule eqName rhs | return none
  let .goals [g] ← rule.applyChecked goal | return none
  return some (← normalizeReducedGoal g)

/-- Wand companion to `reduceFrameConj?`: reduce a residual frame wand `PreservesSup.upperAdjoint
(conj c) R` that the direct `impSplit` couldn't peel over a nested-base lattice (the wand is applied to
an extra inner state coordinate). Build a backward rule from the registered `impReduce` equation
(`upperAdjoint (conj c) R = <closed form>`, e.g. a cost shift `fun m => R (m + c)`) via `mkReduceRule`
and `applyChecked` it; the premise `pre ⊑ <closed form> n s` is the reduced subgoal. Beta-reduce and
`unfoldReducible`-normalize it so the body `R` — and its inner `wp` — is exposed to the normal spec step
instead of stranding in a VC. Run as a fallback, so a flat lattice keeps its direct `impSplit`. -/
private def reduceFrameImp? (goal : MVarId) (rhs : Expr) : VCGenM (Option MVarId) := do
  unless rhs.isAppOf ``Lean.Order.PreservesSup.upperAdjoint do return none
  -- `@PreservesSup.upperAdjoint α inst (conj c) R …`: the slice `conj c` is at index 2; reduce keyed on
  -- its head.
  let some sliceHead := rhs.getAppArgs[2]?.bind (·.getAppFn.constName?) | return none
  let some eqName := (← read).customImpReduces[sliceHead]? | return none
  let some rule ← mkReduceRule eqName rhs | return none
  let .goals [g] ← rule.applyChecked goal | return none
  return some (← normalizeReducedGoal g (betaRhs := true))

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
  if let some gs ← forallIntro? goal target then return .goals scope gs
  if let some g ← targetLetIntro? goal target then return .goals scope [g]
  if let some g ← tripleUnfold? goal target then return .goals scope [g]
  if let some g ← bareWPToLe? goal target then return .goals scope [g]
  if let some gs ← liftedHypBare? scope goal target then return .goals scope gs

  let_expr PartialOrder.rel α inst pre rhs := target
    | return .stop (.noEntailment target)

  -- A previous rule application may have assigned the entailment's sides to fresh metavariables
  -- (e.g. a lattice-split operand). Instantiate those heads so the shape tests below see the
  -- assigned form.
  let pre ← instantiateMVarsIfMVarApp pre
  let rhs ← instantiateMVarsIfMVarApp rhs

  -- Phase 2: close reflexive goals, then drive `pre` toward `⊤`, lifting any pure content so a
  -- later spec application sees a `⊤` precondition.
  if let some gs ← rfl? goal then return .goals scope gs
  if let some (scope, gs) ← normalizePre? scope goal α pre target then return .goals scope gs

  -- Collect new local specs before any strategy that may emit multiple subgoals
  -- (`wpMatch?`, `splitLatticeOp?`) or apply a registered spec (`applySpec`).
  let scope ← scope.collectLocalSpecs goal

  -- Phase 3: shape the `rhs` (reduce an EPost projection, decompose a lattice connective), then
  -- discharge a residual entailment against the lifted hypothesis.
  if let some g ← reduceEPostHead? goal target α inst pre rhs then return .goals scope [g]
  if let some g ← foldUpperAdjointMeet? goal target rhs then return .goals scope [g]
  if let some gs ← splitLatticeOp? goal rhs then return .goals scope gs
  if let some gs ← liftedHyp? scope goal α pre rhs then return .goals scope gs

  -- Phase 4: wp decomposition. The program-shape steps below all consume one unit of fuel
  -- (the `stepLimit` config option) when they make progress.
  if let some info := getWPInfo? rhs then
    trace[Elab.Tactic.Do.vcgen] "📜 Program: {info.prog}"
    -- Stop if the program matches the `until` pattern.
    if ← matchesUntilPattern info.m info.prog then
      return .stop (.untilPatternMatched info.m)
    if let some g ← wpLet? goal info then
      VCGen.burnOne
      return .goals scope [g]
    if let some gs ← wpMatch? goal info then
      VCGen.burnOne
      return .goals scope gs
    if let some g ← wpFVarZeta? goal info then
      VCGen.burnOne
      return .goals scope [g]
    if let some g ← wpHeadReduce? goal info then
      VCGen.burnOne
      return .goals scope [g]
    let f := info.prog.getAppFn
    if f.isConst || f.isFVar then
      VCGen.burnOne
      match ← applyFrame scope goal pre info with
      | .framed scope subgoals => return .goals scope subgoals
      | .notFramed goal info => return ← applySpec scope goal info
    throwError "Failed to decompose weakest precondition for {info.prog}. This should not happen."

  -- Phase 5 (fallback): a registered frame `conj`/wand that the direct split couldn't peel over a
  -- nested-base lattice. `reduceFrameConj?` exposes the `conj`'s `meet`-first connective; `reduceFrameImp?`
  -- reduces the residual wand via its `impReduce` equation. Either way the next iteration's
  -- `splitLatticeOp?`/spec step decomposes the result over all coordinates and specs the inner `wp`.
  if let some g ← reduceFrameConj? goal rhs then return .goals scope [g]
  if let some g ← reduceFrameImp? goal rhs then return .goals scope [g]

  return .stop (.noProgress pre rhs)

end VCGen

end Lean.Elab.Tactic.Do.Internal
