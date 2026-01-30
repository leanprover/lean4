/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Elab.Tactic.Grind.Basic
import Lean.Meta.Tactic.TryThis
import Lean.Meta.Tactic.Grind.Solve
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Search
import Lean.Meta.Tactic.Grind.Arith.Linear.Search
import Lean.Meta.Tactic.Grind.Arith.CommRing.EqCnstr
import Lean.Meta.Tactic.Grind.AC.Eq
import Lean.Meta.Tactic.Grind.EMatch
import Lean.Meta.Tactic.Grind.EMatchTheorem
import Lean.Meta.Tactic.Grind.PP
import Lean.Meta.Tactic.Grind.Internalize
import Lean.Meta.Tactic.Grind.Intro
import Lean.Meta.Tactic.Grind.Split
import Lean.Meta.Tactic.Grind.Anchor
import Lean.Meta.Tactic.Grind.Arith.CommRing.PP
import Lean.Meta.Tactic.Grind.Arith.Linear.PP
import Lean.Meta.Tactic.Grind.AC.PP
import Lean.Meta.Tactic.ExposeNames
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.RenameInaccessibles
import Lean.Elab.Tactic.Grind.Filter
import Lean.Elab.Tactic.Grind.Anchor
import Lean.Elab.Tactic.Grind.ShowState
import Lean.Elab.Tactic.Grind.Config
import Lean.Elab.Tactic.Grind.Param
import Lean.Elab.SetOption
namespace Lean.Elab.Tactic.Grind

def showStateAt (ref : Syntax) (filter? : Option (TSyntax `grind_filter)) : GrindTacticM Unit := do
  if let goal :: _ := (← getGoals) then
    withRef ref <| goal.withContext do
      let filter ← elabFilter filter?
      showState filter (isSilent := true)
  else
    logAt ref (severity := .information) (isSilent := true) "no grind state"

def evalSepTactics (stx : Syntax) : GrindTacticM Unit := do
  for arg in stx.getArgs, i in *...stx.getArgs.size do
    if i % 2 == 0 then
      match arg with
      | `(Parser.Tactic.Grind.grindStep| $tac:grind) => evalGrindTactic tac
      | `(Parser.Tactic.Grind.grindStep| $tac:grind | $[$filter?]?) =>
        showStateAt arg filter?
        evalGrindTactic tac
        showStateAt arg[1] filter?
      | _ => throwUnsupportedSyntax
    else
      saveTacticInfoForToken arg

@[builtin_grind_tactic grindSeq1Indented]
def evalGrindSeq1Indented : GrindTactic := fun stx =>
  evalSepTactics stx[0]

@[builtin_grind_tactic grindSeqBracketed]
def evalGrindSeqBracketed : GrindTactic := fun stx => do
  let initInfo ← mkInitialTacticInfo stx[0]
  withRef stx[2] <| closeUsingOrAdmit do
    -- save state before/after entering focus on `{`
    withInfoContext (pure ()) initInfo
    evalSepTactics stx[1]

@[builtin_grind_tactic grindSeq]
def evalGrindSeq : GrindTactic := fun stx =>
  evalGrindTactic stx[0]

@[builtin_grind_tactic Parser.Tactic.Grind.«done»] def evalDone : GrindTactic := fun _ =>
  done

@[builtin_grind_tactic Parser.Tactic.Grind.«sorry»] def evalSorry : GrindTactic := fun _ => do
  let goal ← getMainGoal
  goal.mvarId.admit
  replaceMainGoal []

@[builtin_grind_tactic skip] def evalSkip : GrindTactic := fun _ =>
  return ()

@[builtin_grind_tactic paren] def evalParen : GrindTactic := fun stx =>
  evalGrindTactic stx[1]

open Meta Grind

@[builtin_grind_tactic finish] def evalFinish : GrindTactic := fun stx => withMainContext do
  let `(grind| finish $[$configItems]* $[only%$only]? $[[$params?,*]]?) := stx | throwUnsupportedSyntax
  withConfigItems configItems do
  let params := params?.getD {}
  withParams (← read).params params only.isSome do
    let goal ← getMainGoal
    if let some goal ← liftGrindM <| solve goal then
      let params := (← read).params
      let result ← liftGrindM do mkResult params (some goal)
      throwError "`finish` failed\n{← result.toMessageData}"
    else
      replaceMainGoal []

/--
Helper function to executing "check" tactics that return a flag indicating
whether they made progress or not.
If the goal is not inconsistent and progress has been made,
`pp?` is executed to produce an info message.
-/
def evalCheck (tacticName : Name) (k : GoalM Bool)
    (pp? : Goal → MetaM (Option MessageData)) : GrindTacticM Unit := do
  let recover := (← read).recover
  liftGoalM do
    let progress ← k
    unless progress do
      throwError "`{tacticName}` failed"
    processNewFacts
    unless (← Grind.getConfig).verbose do return ()
    unless recover do return ()
    if (← get).inconsistent then return ()
    let some msg ← pp? (← get) | return ()
    logInfo msg

@[builtin_grind_tactic lia] def evalLIA : GrindTactic := fun _ =>
  evalCheck `lia Arith.Cutsat.check Arith.Cutsat.pp?

@[builtin_grind_tactic linarith] def evalLinarith : GrindTactic := fun _ => do
  evalCheck `linarith Arith.Linear.check Arith.Linear.pp?

@[builtin_grind_tactic ring] def evalRing : GrindTactic := fun _ => do
  evalCheck `ring Arith.CommRing.check' Arith.CommRing.pp?

@[builtin_grind_tactic ac] def evalAC : GrindTactic := fun _ => do
  evalCheck `ac AC.check' AC.pp?

def logTheoremAnchor (proof : Expr) : TermElabM Unit := do
  let stx ← getRef
  Term.addTermInfo' stx proof

def ematchThms (only : Bool) (thms : Array EMatchTheorem) : GrindTacticM Unit := do
  -- **TODO**: add `instantiate` action that takes `thms`
  let progress ← liftGoalM do
    let thms ← thms.mapM (preprocessTheorem · 0)
    if only then ematchOnly thms else ematch thms
  unless progress do
    throwError "`instantiate` tactic failed to instantiate new facts, use `show_patterns` to see active theorems and their patterns."
  liftAction Action.assertAll

@[builtin_grind_tactic instantiate] def evalInstantiate : GrindTactic := fun stx => withMainContext do
  let `(grind| instantiate $[ only%$only ]? $[ approx ]? $[ [ $[$thmRefs?:thm],* ] ]?) := stx | throwUnsupportedSyntax
  let goal ← getMainGoal
  let only := only.isSome
  let initThms ← if only then goal.getActiveMatchEqTheorems else pure #[]
  let mut thms := initThms
  if let some thmRefs := thmRefs? then
    for thmRef in thmRefs do
      match thmRef with
      -- **Note**: Delete `namespace` modifier. We should use a custom `grind` attribute for this.
      | `(Parser.Tactic.Grind.thm| namespace $ns:ident) =>
        let namespaceName := ns.getId
        let scopedThms ← Grind.grindExt.getEMatchTheoremsForNamespace namespaceName
        thms := thms ++ scopedThms
      | `(Parser.Tactic.Grind.thm| #$anchor:hexnum) => thms := thms ++ (← withRef thmRef <| elabLocalEMatchTheorem anchor)
      | `(Parser.Tactic.Grind.thm| $[$mod?:grindMod]? $id:ident) => thms := thms ++ (← withRef thmRef <| elabThm mod? id false)
      | `(Parser.Tactic.Grind.thm| ! $[$mod?:grindMod]? $id:ident) => thms := thms ++ (← withRef thmRef <| elabThm mod? id true)
      | _ => throwErrorAt thmRef "unexpected theorem reference"
  ematchThms only thms
where
  collectThms (anchorRef : AnchorRef) (thms : PArray EMatchTheorem) : StateT (Array EMatchTheorem) GrindTacticM Unit := do
    let mut found : Std.HashSet Expr := {}
    for thm in thms do
      -- **Note**: `anchors` are cached using pointer addresses, if this is a performance issue, we should
      -- cache the theorem types.
      let type ← inferType thm.proof
      let anchor ← liftGrindM <| getAnchor type
      if anchorRef.matches anchor then
        -- **Note**: We display the anchor term at most once.
        unless found.contains type do
          logTheoremAnchor thm.proof
          found := found.insert type
        modify (·.push thm)

  elabLocalEMatchTheorem (anchor : TSyntax `hexnum) : GrindTacticM (Array EMatchTheorem) := withRef anchor do
    let anchorRef ← elabAnchorRef anchor
    let goal ← getMainGoal
    let thms ← StateT.run' (s := #[]) do
      collectThms anchorRef goal.ematch.thms
      collectThms anchorRef goal.ematch.newThms
      get
    if thms.isEmpty then
      throwError "no local theorems"
    return thms

  ensureNoMinIndexable (minIndexable : Bool) : MetaM Unit := do
    if minIndexable then
      throwError "redundant modifier `!` in `grind` parameter"

  elabEMatchTheorem (declName : Name) (kind : Grind.EMatchTheoremKind) (minIndexable : Bool) : GrindTacticM (Array EMatchTheorem) := do
    let params := (← read).params
    let info ← getAsyncConstInfo declName
    match info.kind with
    | .thm | .axiom | .ctor =>
      match kind with
      | .eqBoth gen =>
        ensureNoMinIndexable minIndexable
        let thm₁ ← Grind.mkEMatchTheoremForDecl declName (.eqLhs gen) params.symPrios
        let thm₂ ← Grind.mkEMatchTheoremForDecl declName (.eqRhs gen) params.symPrios
        return #[thm₁, thm₂]
      | _ =>
        if kind matches .eqLhs _ | .eqRhs _ then
          ensureNoMinIndexable minIndexable
        let thm ← Grind.mkEMatchTheoremForDecl declName kind params.symPrios (minIndexable := minIndexable)
        return #[thm]
    | .defn =>
      if (← isReducible declName) then
        throwError "`{.ofConstName declName}` is a reducible definition, `grind` automatically unfolds them"
      if !kind.isEqLhs && !kind.isDefault then
        throwError "invalid `grind` parameter, `{.ofConstName declName}` is a definition, the only acceptable (and redundant) modifier is '='"
      ensureNoMinIndexable minIndexable
      let some thms ← Grind.mkEMatchEqTheoremsForDef? declName
        | throwError "failed to generate equation theorems for `{.ofConstName declName}`"
      return thms
    | _ =>
      throwError "invalid `grind` parameter, `{.ofConstName declName}` is not a theorem, definition, or inductive type"

  elabThm
      (mod? : Option (TSyntax `Lean.Parser.Attr.grindMod))
      (id : TSyntax `ident)
      (minIndexable : Bool) : GrindTacticM (Array EMatchTheorem) := do
    let declName ← realizeGlobalConstNoOverloadWithInfo id
    let kind ← if let some mod := mod? then Grind.getAttrKindCore mod else pure .infer
    match kind with
    | .ematch .user =>
      ensureNoMinIndexable minIndexable
      let params := (← read).params
      let thms := params.extensions.find (.decl declName)
      let thms := thms.filter fun thm => thm.kind == .user
      if thms.isEmpty then
        throwError "invalid use of `usr` modifier, `{.ofConstName declName}` does not have patterns specified with the command `grind_pattern`"
      return thms.toArray
    | .ematch kind =>
      elabEMatchTheorem declName kind minIndexable
    | .infer =>
      let goal ← getMainGoal
      let thms := goal.ematch.thmMap.find (.decl declName)
      if thms.isEmpty then
        elabEMatchTheorem declName (.default false) minIndexable
      else
        return thms.toArray
    | .cases _ | .intro | .inj | .ext | .symbol _ | .funCC | .norm .. | .unfold =>
      throwError "invalid modifier"

def logAnchor (c : SplitInfo) : TermElabM Unit := do
  let e := c.getExpr
  let stx ← getRef
  if e.isFVar || e.isConst then
    /-
    **Note**: When `e` is a constant or free variable, the hover displays `e`
    -/
    Term.addTermInfo' stx e
  else if (← isType e) then
    /-
    **Note**: If `e` is a type, we create a fake `sorry` to force `e` to be displayed
    when we hover over the anchor.
    We wrap the `sorry` with `id` to ensure the hover will not display `sorry : e`
    -/
    let e ← mkSorry e (synthetic := false)
    let e ← mkId e
    Term.addTermInfo' stx e
  else
    /-
    **Note**: `e` and its type are displayed when hovering over the anchor.
    -/
    Term.addTermInfo' stx e (isDisplayableTerm := True)

def split? (c : SplitInfo) : Action := fun goal kna kp => do
  let (.ready numCases isRec _, goal) ← GoalM.run goal (checkSplitStatus c)
    | throwError "`cases` tactic failed, case-split is not ready{indentExpr c.getExpr}"
  let gen := goal.getGeneration c.getExpr
  let genNew := if numCases > 1 || isRec then gen+1 else gen
  let a : Action :=
    Action.splitCore c numCases isRec (stopAtFirstFailure := false) (compress := false) >> Action.intros genNew >> Action.assertAll
  a goal kna kp

@[builtin_grind_tactic cases] def evalCases : GrindTactic := fun stx => do
  let `(grind| cases #$anchor:hexnum) := stx | throwUnsupportedSyntax
  let anchorRef ← elabAnchorRef anchor
  let goal ← getMainGoal
  let candidates := goal.split.candidates
  let c ← liftGrindM <| goal.withContext do
    for c in candidates do
      let anchor ← c.getAnchor
      if anchorRef.matches anchor then
        return c
    throwError "`cases` tactic failed, invalid anchor"
  goal.withContext <| withRef anchor <| logAnchor c
  liftAction <| split? c

def mkCasesSuggestions (candidates : Array SplitCandidateWithAnchor) (numDigits : Nat) : MetaM (Array Tactic.TryThis.Suggestion) := do
  candidates.mapM fun { anchor, e, .. } => do
    let anchorStx ← mkAnchorSyntax numDigits anchor
    let tac ← `(grind| cases $anchorStx:anchor)
    let msg ← addMessageContext m!"{tac} for{indentExpr e}"
    return {
      suggestion   := .tsyntax tac
      messageData? := some msg
    }

@[builtin_grind_tactic casesTrace] def evalCasesTrace : GrindTactic := fun stx => withMainContext do
  let `(grind| cases? $[$filter?]?) := stx | throwUnsupportedSyntax
  let filter ← elabFilter filter?
  let { candidates, numDigits } ← liftGoalM <| getSplitCandidateAnchors filter.eval
  let suggestions ← mkCasesSuggestions candidates numDigits
  Tactic.TryThis.addSuggestions stx suggestions
  return ()

@[builtin_grind_tactic casesNext] def evalCasesNext : GrindTactic := fun _ => do
  liftAction (Action.splitNext (stopAtFirstFailure := false))

@[builtin_grind_tactic Parser.Tactic.Grind.focus] def evalFocus : GrindTactic := fun stx => do
  let mkInfo ← mkInitialTacticInfo stx[0]
  focus do
    -- show focused state on `focus`
    withInfoContext (pure ()) mkInfo
    evalGrindTactic stx[1]

@[builtin_grind_tactic allGoals] def evalAllGoals : GrindTactic := fun stx => do
  let goals ← getGoals
  let mut goalsNew := #[]
  let mut abort := false
  for goal in goals do
    unless (← goal.mvarId.isAssigned) do
      setGoals [goal]
      let saved ← saveState
      abort ← Grind.tryCatch
        (do
          evalGrindTactic stx[1]
          pure abort)
        (fun ex => do
          if (← read).recover then
            logException ex
            let msgLog ← Core.getMessageLog
            saved.restore
            Core.setMessageLog msgLog
            admitGoal goal.mvarId
            pure true
          else
            throw ex)
      goalsNew := goalsNew ++ (← getUnsolvedGoals)
  if abort then
    throwAbortTactic
  setGoals goalsNew.toList

@[builtin_grind_tactic withAnnotateState] def evalWithAnnotateState : GrindTactic := fun stx =>
  withTacticInfoContext stx[1] do
  evalGrindTactic stx[2]

@[builtin_grind_tactic anyGoals] def evalAnyGoals : GrindTactic := fun stx => do
  let goals ← getGoals
  let mut goalsNew := #[]
  let mut succeeded := false
  for goal in goals do
    unless (← goal.mvarId.isAssigned) do
      setGoals [goal]
      try
        evalGrindTactic stx[1]
        goalsNew := goalsNew ++ (← getUnsolvedGoals)
        succeeded := true
      catch _ =>
        goalsNew := goalsNew.push goal
  unless succeeded do
    throwError "Tactic failed on all goals:{indentD stx[1]}"
  setGoals goalsNew.toList

public def renameInaccessibles (mvarId : MVarId) (hs : TSyntaxArray ``binderIdent) : GrindTacticM MVarId := do
  let mvarId ← Tactic.renameInaccessibles mvarId hs
  unless hs.isEmpty do liftGrindM <| resetAnchors
  return mvarId

@[builtin_grind_tactic «next»] def evalNext : GrindTactic := fun stx => do
  let `(grind| next%$nextTk $hs* =>%$arr $seq:grindSeq) := stx | throwUnsupportedSyntax
  let goal :: goals ← getUnsolvedGoals | throwNoGoalsToBeSolved
  let mvarId ← renameInaccessibles goal.mvarId hs
  let goal := { goal with mvarId }
  setGoals [goal]
  goal.mvarId.setTag Name.anonymous
  withCaseRef arr seq <| closeUsingOrAdmit <| withTacticInfoContext (mkNullNode #[nextTk, arr]) <|
    evalGrindTactic stx[3]
  setGoals goals

@[builtin_grind_tactic nestedTacticCore] def evalNestedTactic : GrindTactic := fun stx => do
  let `(grind| tactic%$tacticTk =>%$arr $seq:tacticSeq) := stx | throwUnsupportedSyntax
  let goal ← getMainGoal
  let recover := (← read).recover
  discard <| Tactic.run goal.mvarId <| withCaseRef arr seq <| Tactic.closeUsingOrAdmit
    <| Tactic.withTacticInfoContext (mkNullNode #[tacticTk, arr])
    <| Tactic.withRecover recover <| evalTactic seq
  replaceMainGoal []

@[builtin_grind_tactic «first»] partial def evalFirst : GrindTactic := fun stx => do
  let `(grind| first $[($s:grindSeq)]*) := stx | throwUnsupportedSyntax
  loop s 0
where
  loop (s : Array (TSyntax ``Parser.Tactic.Grind.grindSeq)) (i : Nat) :=
    if i == s.size - 1 then
      evalGrindTactic s[i]!
    else
      evalGrindTactic s[i]! <|> loop s (i+1)

@[builtin_grind_tactic failIfSuccess] def evalFailIfSuccess : GrindTactic := fun stx =>
  Term.withoutErrToSorry <| withoutRecover do
    let tactic := stx[1]
    if (← try evalGrindTactic tactic; pure true catch _ => pure false) then
      throwError "The tactic provided to `fail_if_success` succeeded but was expected to fail:{indentD stx[1]}"

@[builtin_grind_tactic «fail»] def evalFail : GrindTactic := fun stx => do
  let goals ← getGoals
  let goalsMsg := MessageData.joinSep (goals.map (MessageData.ofGoal ·.mvarId)) m!"\n\n"
  match stx with
  | `(grind| fail)          => throwError "Failed: `fail` tactic was invoked\n{goalsMsg}"
  | `(grind| fail $msg:str) => throwError "{msg.getString}\n{goalsMsg}"
  | _ => throwUnsupportedSyntax

@[builtin_grind_tactic «renameI»] def evalRenameInaccessibles : GrindTactic := fun stx => do
  let `(grind| rename_i $hs*) := stx | throwUnsupportedSyntax
  let goal ← getMainGoal
  let mvarId ← renameInaccessibles goal.mvarId hs
  replaceMainGoal [{ goal with mvarId }]

@[builtin_grind_tactic exposeNames] def evalExposeNames : GrindTactic := fun _ => do
  let goal ← getMainGoal
  let mvarId ← goal.mvarId.exposeNames
  liftGrindM <| resetAnchors
  replaceMainGoal [{ goal with mvarId }]

@[builtin_grind_tactic setOption] def elabSetOption : GrindTactic := fun stx => do
  let options ← Elab.elabSetOption stx[1] stx[3]
  withOptions (fun _ => options) do evalGrindTactic stx[5]

@[builtin_grind_tactic setConfig] def elabSetConfig : GrindTactic := fun stx => do
  let `(grind| set_config $[$items:configItem]* in $seq:grindSeq) := stx | throwUnsupportedSyntax
  withConfigItems items do evalGrindTactic seq

@[builtin_grind_tactic mbtc] def elabMBTC : GrindTactic := fun _ => do
  liftGoalM do
    discard <| Solvers.check
    if (← get).inconsistent then
      return ()
    let progress ← Solvers.mbtc
    unless progress do
      throwError "`mbtc` tactic failed to generate new candidate case-splits."

end Lean.Elab.Tactic.Grind
