/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Diagnostics
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Assumption
import Lean.Meta.Tactic.Contradiction
import Lean.Meta.Tactic.Refl
import Lean.Elab.Binders
import Lean.Elab.Open
import Lean.Elab.Eval
import Lean.Elab.SetOption
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Do

namespace Lean.Elab.Tactic
open Meta
open Parser.Tactic

@[builtin_tactic withAnnotateState, builtin_incremental] def evalWithAnnotateState : Tactic :=
  fun stx =>
    withTacticInfoContext stx[1] do
    Term.withNarrowedArgTacticReuse (argIdx := 2) evalTactic stx

@[builtin_tactic Lean.Parser.Tactic.«done»] def evalDone : Tactic := fun _ =>
  done

open Language in
/--
Evaluates a tactic script in form of a syntax node with alternating tactics and separators as
children.
 -/
partial def evalSepTactics : Tactic := goEven
where
  -- `stx[0]` is the next tactic step, if any
  goEven stx := do
    if stx.getNumArgs == 0 then
      return
    let tac := stx[0]
    /-
    Each `goEven` step creates three promises under incrementality and reuses their older versions
    where possible:
    * `finished` is resolved when `tac` finishes execution; if `tac` is wholly unchanged from the
      previous version, its state is reused and `tac` execution is skipped. Note that this promise
      is never turned into a `SnapshotTask` and added to the snapshot tree as incremental reporting
      is already covered by the next two promises.
    * `inner` is passed to `tac` if it is marked as supporting incrementality and can be used for
      reporting and partial reuse inside of it; if the tactic is unsupported or `finished` is wholly
      reused, it is ignored.
    * `next` is used as the context when invoking `goOdd` and thus eventually used for the next
      `goEven` step. Thus, the incremental state of a tactic script is ultimately represented as a
      chain of `next` snapshots. Its reuse is disabled if `tac` or its following separator are
      changed in any way.
    -/
    let mut oldInner? := none
    if let some snap := (← readThe Term.Context).tacSnap? then
      if let some old := snap.old? then
        let oldParsed := old.val.get
        oldInner? := oldParsed.inner? |>.map (⟨oldParsed.stx, ·⟩)
    -- compare `stx[0]` for `finished`/`next` reuse, focus on remainder of script
    Term.withNarrowedTacticReuse (stx := stx) (fun stx => (stx[0], mkNullNode stx.getArgs[1:])) fun stxs => do
      let some snap := (← readThe Term.Context).tacSnap?
        | do evalTactic tac; goOdd stxs
      let mut reusableResult? := none
      let mut oldNext? := none
      if let some old := snap.old? then
        -- `tac` must be unchanged given the narrow above; let's reuse `finished`'s state!
        let oldParsed := old.val.get
        if let some state := oldParsed.finished.get.state? then
          reusableResult? := some ((), state)
          -- only allow `next` reuse in this case
          oldNext? := oldParsed.next.get? 0 |>.map (⟨old.stx, ·⟩)

      -- For `tac`'s snapshot task range, disregard synthetic info as otherwise
      -- `SnapshotTree.findInfoTreeAtPos` might choose the wrong snapshot: for example, when
      -- hovering over a `show` tactic, we should choose the info tree in `finished` over that in
      -- `inner`, which points to execution of the synthesized `refine` step and does not contain
      -- the full info. In most other places, siblings in the snapshot tree have disjoint ranges and
      -- so this issue does not occur.
      let mut range? := tac.getRange? (canonicalOnly := true)
      -- Include trailing whitespace in the range so that `goalsAs?` does not have to wait for more
      -- snapshots than necessary.
      if let some range := range? then
        range? := some { range with stop := ⟨range.stop.byteIdx + tac.getTrailingSize⟩ }
      withAlwaysResolvedPromise fun next => do
        withAlwaysResolvedPromise fun finished => do
          withAlwaysResolvedPromise fun inner => do
            snap.new.resolve {
              desc := tac.getKind.toString
              diagnostics := .empty
              stx := tac
              inner? := some { range?, task := inner.result }
              finished := { range?, task := finished.result }
              next := #[{ range? := stxs.getRange?, task := next.result }]
            }
            -- Run `tac` in a fresh info tree state and store resulting state in snapshot for
            -- incremental reporting, then add back saved trees. Here we rely on `evalTactic`
            -- producing at most one info tree as otherwise `getInfoTreeWithContext?` would panic.
            let trees ← getResetInfoTrees
            try
              let (_, state) ← withRestoreOrSaveFull reusableResult?
                  -- set up nested reuse; `evalTactic` will check for `isIncrementalElab`
                  (tacSnap? := some { old? := oldInner?, new := inner }) do
                Term.withReuseContext tac do
                  evalTactic tac
              finished.resolve {
                diagnostics := (← Language.Snapshot.Diagnostics.ofMessageLog
                  (← Core.getAndEmptyMessageLog))
                infoTree? := (← Term.getInfoTreeWithContext?)
                state? := state
              }
            finally
              modifyInfoState fun s => { s with trees := trees ++ s.trees }

        withTheReader Term.Context ({ · with tacSnap? := some {
          new := next
          old? := oldNext?
        } }) do
          goOdd stxs
  -- `stx[0]` is the next separator, if any
  goOdd stx := do
    if stx.getNumArgs == 0 then
      return
    saveTacticInfoForToken stx[0] -- add `TacticInfo` node for `;`
    -- disable further reuse on separator change as to not reuse wrong `TacticInfo`
    Term.withNarrowedTacticReuse (fun stx => (stx[0], mkNullNode stx.getArgs[1:])) goEven stx

@[builtin_tactic seq1] def evalSeq1 : Tactic := fun stx =>
  evalSepTactics stx[0]

@[builtin_tactic paren, builtin_incremental] def evalParen : Tactic :=
  Term.withNarrowedArgTacticReuse 1 evalTactic

def isCheckpointableTactic (arg : Syntax) : TacticM Bool := do
  -- TODO: make it parametric
  let kind := arg.getKind
  return kind == ``Lean.Parser.Tactic.save

/--
Takes a `sepByIndent tactic "; "`, and inserts `checkpoint` blocks for `save` tactics.

Input:
```
  a
  b
  save
  c
  d
  save
  e
```

Output:
```
  checkpoint
    a
    b
    save
  checkpoint
    c
    d
    save
  e
```
-/
-- Note that we need to preserve the separators to show the right goals after semicolons.
def addCheckpoints (stx : Syntax) : TacticM Syntax := do
  if !(← stx.getSepArgs.anyM isCheckpointableTactic) then return stx
  -- do not checkpoint checkpointable tactic by itself to prevent infinite recursion
  -- TODO: rethink approach if we add non-trivial checkpointable tactics
  if stx.getNumArgs <= 2 then return stx
  let mut currentCheckpointBlock := #[]
  let mut output := #[]
  -- `+ 1` to account for optional trailing separator
  for i in [:(stx.getArgs.size + 1) / 2] do
    let tac := stx[2*i]
    let sep? := stx.getArgs[2*i+1]?
    if (← isCheckpointableTactic tac) then
      let checkpoint : Syntax :=
        mkNode ``checkpoint #[
          mkAtomFrom tac "checkpoint",
          mkNode ``tacticSeq #[
            mkNode ``tacticSeq1Indented #[
              -- HACK: null node is not a valid tactic, but prevents infinite loop
              mkNullNode (currentCheckpointBlock.push (mkNullNode #[tac]))
            ]
          ]
        ]
      currentCheckpointBlock := #[]
      output := output.push checkpoint
      if let some sep := sep? then output := output.push sep
    else
      currentCheckpointBlock := currentCheckpointBlock.push tac
      if let some sep := sep? then currentCheckpointBlock := currentCheckpointBlock.push sep
  output := output ++ currentCheckpointBlock
  return stx.setArgs output

@[builtin_tactic tacticSeq1Indented, builtin_incremental]
def evalTacticSeq1Indented : Tactic :=
  Term.withNarrowedArgTacticReuse (argIdx := 0) evalSepTactics

@[builtin_tactic tacticSeqBracketed, builtin_incremental]
def evalTacticSeqBracketed : Tactic := fun stx => do
  let initInfo ← mkInitialTacticInfo stx[0]
  withRef stx[2] <| closeUsingOrAdmit do
    -- save state before/after entering focus on `{`
    withInfoContext (pure ()) initInfo
    Term.withNarrowedArgTacticReuse (argIdx := 1) evalSepTactics stx

@[builtin_tactic Lean.cdot, builtin_incremental]
def evalTacticCDot : Tactic := fun stx => do
  -- adjusted copy of `evalTacticSeqBracketed`; we used to use the macro
  -- ``| `(tactic| $cdot:cdotTk $tacs) => `(tactic| {%$cdot ($tacs) }%$cdot)``
  -- but the token antiquotation does not copy trailing whitespace, leading to
  -- differences in the goal display (#2153)
  let initInfo ← mkInitialTacticInfo stx[0]
  withCaseRef stx[0] stx[1] <| closeUsingOrAdmit do
    -- save state before/after entering focus on `·`
    withInfoContext (pure ()) initInfo
    Term.withNarrowedArgTacticReuse (argIdx := 1) evalTactic stx

@[builtin_tactic Parser.Tactic.focus, builtin_incremental] def evalFocus : Tactic := fun stx => do
  let mkInfo ← mkInitialTacticInfo stx[0]
  focus do
    -- show focused state on `focus`
    withInfoContext (pure ()) mkInfo
    Term.withNarrowedArgTacticReuse (argIdx := 1) evalTactic stx

private def getOptRotation (stx : Syntax) : Nat :=
  if stx.isNone then 1 else stx[0].toNat

@[builtin_tactic Parser.Tactic.rotateLeft] def evalRotateLeft : Tactic := fun stx => do
  let n := getOptRotation stx[1]
  setGoals <| (← getGoals).rotateLeft n

@[builtin_tactic Parser.Tactic.rotateRight] def evalRotateRight : Tactic := fun stx => do
  let n := getOptRotation stx[1]
  setGoals <| (← getGoals).rotateRight n

@[builtin_tactic Parser.Tactic.open] def evalOpen : Tactic := fun stx => do
  let `(tactic| open $decl in $tac) := stx | throwUnsupportedSyntax
  try
    pushScope
    let openDecls ← elabOpenDecl decl
    withTheReader Core.Context (fun ctx => { ctx with openDecls := openDecls }) do
      evalTactic tac
  finally
    popScope

@[builtin_tactic Parser.Tactic.set_option] def elabSetOption : Tactic := fun stx => do
  let options ← Elab.elabSetOption stx[1] stx[3]
  withOptions (fun _ => options) do
    try
      evalTactic stx[5]
    finally
      if stx[1].getId == `diagnostics then
        reportDiag

@[builtin_tactic Parser.Tactic.allGoals] def evalAllGoals : Tactic := fun stx => do
  let mvarIds ← getGoals
  let mut mvarIdsNew := #[]
  let mut abort := false
  let mut mctxSaved ← getMCtx
  for mvarId in mvarIds do
    unless (← mvarId.isAssigned) do
      setGoals [mvarId]
      abort ← Tactic.tryCatch
        (do
          evalTactic stx[1]
          pure abort)
        (fun ex => do
          if (← read).recover then
            logException ex
            pure true
          else
            throw ex)
      mvarIdsNew := mvarIdsNew ++ (← getUnsolvedGoals)
  if abort then
    setMCtx mctxSaved
    mvarIds.forM fun mvarId => unless (← mvarId.isAssigned) do admitGoal mvarId
    throwAbortTactic
  setGoals mvarIdsNew.toList

@[builtin_tactic Parser.Tactic.anyGoals] def evalAnyGoals : Tactic := fun stx => do
  let mvarIds ← getGoals
  let mut mvarIdsNew := #[]
  let mut succeeded := false
  for mvarId in mvarIds do
    unless (← mvarId.isAssigned) do
      setGoals [mvarId]
      try
        evalTactic stx[1]
        mvarIdsNew := mvarIdsNew ++ (← getUnsolvedGoals)
        succeeded := true
      catch _ =>
        mvarIdsNew := mvarIdsNew.push mvarId
  unless succeeded do
    throwError "failed on all goals"
  setGoals mvarIdsNew.toList

@[builtin_tactic tacticSeq, builtin_incremental]
def evalTacticSeq : Tactic :=
  Term.withNarrowedArgTacticReuse (argIdx := 0) evalTactic

partial def evalChoiceAux (tactics : Array Syntax) (i : Nat) : TacticM Unit :=
  if h : i < tactics.size then
    let tactic := tactics[i]
    catchInternalId unsupportedSyntaxExceptionId
      (evalTactic tactic)
      (fun _ => evalChoiceAux tactics (i+1))
  else
    throwUnsupportedSyntax

@[builtin_tactic choice] def evalChoice : Tactic := fun stx =>
  evalChoiceAux stx.getArgs 0

@[builtin_tactic skip] def evalSkip : Tactic := fun _ => pure ()

@[builtin_tactic unknown] def evalUnknown : Tactic := fun stx => do
  addCompletionInfo <| CompletionInfo.tactic stx

@[builtin_tactic failIfSuccess] def evalFailIfSuccess : Tactic := fun stx =>
  Term.withoutErrToSorry <| withoutRecover do
    let tactic := stx[1]
    if (← try evalTactic tactic; pure true catch _ => pure false) then
      throwError "tactic succeeded"

@[builtin_tactic traceState] def evalTraceState : Tactic := fun _ => do
  let gs ← getUnsolvedGoals
  addRawTrace (goalsToMessageData gs)

@[builtin_tactic traceMessage] def evalTraceMessage : Tactic := fun stx => do
  match stx[1].isStrLit? with
  | none     => throwIllFormedSyntax
  | some msg => withRef stx[0] <| addRawTrace msg

@[builtin_tactic Lean.Parser.Tactic.assumption] def evalAssumption : Tactic := fun _ =>
  -- The `withAssignableSyntheticOpaque` is needed here to accommodate
  -- `assumption` after `refine`.
  -- See https://github.com/leanprover/lean4/issues/2361
  liftMetaTactic fun mvarId => withAssignableSyntheticOpaque do mvarId.assumption; pure []

@[builtin_tactic Lean.Parser.Tactic.contradiction] def evalContradiction : Tactic := fun _ =>
  liftMetaTactic fun mvarId => do mvarId.contradiction; pure []

@[builtin_tactic Lean.Parser.Tactic.eqRefl] def evalRefl : Tactic := fun _ =>
  liftMetaTactic fun mvarId => do mvarId.refl; pure []

@[builtin_tactic Lean.Parser.Tactic.intro] def evalIntro : Tactic := fun stx => do
  match stx with
  | `(tactic| intro)                   => introStep none `_
  | `(tactic| intro $h:ident)          => introStep h h.getId
  | `(tactic| intro _%$tk)             => introStep tk `_
  /- Type ascription -/
  | `(tactic| intro ($h:ident : $type:term)) => introStep h h.getId type
  /- We use `@h` at the match-discriminant to disable the implicit lambda feature -/
  | `(tactic| intro $pat:term)         => evalTactic (← `(tactic| intro h; match @h with | $pat:term => ?_; try clear h))
  | `(tactic| intro $h:term $hs:term*) => evalTactic (← `(tactic| intro $h:term; intro $hs:term*))
  | _ => throwUnsupportedSyntax
where
  introStep (ref : Option Syntax) (n : Name) (typeStx? : Option Syntax := none) : TacticM Unit := do
    let fvarId ← liftMetaTacticAux fun mvarId => do
      let (fvarId, mvarId) ← mvarId.intro n
      pure (fvarId, [mvarId])
    if let some typeStx := typeStx? then
      withMainContext do
        let type ← Term.withSynthesize (postpone := .yes) <| Term.elabType typeStx
        let fvar := mkFVar fvarId
        let fvarType ← inferType fvar
        unless (← isDefEqGuarded type fvarType) do
          throwError "type mismatch at `intro {fvar}`{← mkHasTypeButIsExpectedMsg fvarType type}"
        liftMetaTactic fun mvarId => return [← mvarId.replaceLocalDeclDefEq fvarId type]
    if let some stx := ref then
      withMainContext do
        Term.addLocalVarInfo stx (mkFVar fvarId)

@[builtin_tactic Lean.Parser.Tactic.introMatch] def evalIntroMatch : Tactic := fun stx => do
  let matchAlts := stx[1]
  let stxNew ← liftMacroM <| Term.expandMatchAltsIntoMatchTactic stx matchAlts
  withMacroExpansion stx stxNew <| evalTactic stxNew

@[builtin_tactic «intros»] def evalIntros : Tactic := fun stx =>
  match stx with
  | `(tactic| intros) => liftMetaTactic fun mvarId => do
    let (_, mvarId) ← mvarId.intros
    return [mvarId]
  | `(tactic| intros $ids*) => do
    let fvars ← liftMetaTacticAux fun mvarId => do
      let (fvars, mvarId) ← mvarId.introN ids.size (ids.map getNameOfIdent').toList
      return (fvars, [mvarId])
    withMainContext do
      for stx in ids, fvar in fvars do
        Term.addLocalVarInfo stx (mkFVar fvar)
  | _ => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.revert] def evalRevert : Tactic := fun stx =>
  match stx with
  | `(tactic| revert $hs*) => do
     let (_, mvarId) ← (← getMainGoal).revert (← getFVarIds hs)
     replaceMainGoal [mvarId]
  | _                     => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.clear] def evalClear : Tactic := fun stx =>
  match stx with
  | `(tactic| clear $hs*) => do
    let fvarIds ← getFVarIds hs
    let fvarIds ← withMainContext <| sortFVarIds fvarIds
    for fvarId in fvarIds.reverse do
      withMainContext do
        let mvarId ← (← getMainGoal).clear fvarId
        replaceMainGoal [mvarId]
  | _ => throwUnsupportedSyntax

def forEachVar (hs : Array Syntax) (tac : MVarId → FVarId → MetaM MVarId) : TacticM Unit := do
  for h in hs do
    withMainContext do
      let fvarId ← getFVarId h
      let mvarId ← tac (← getMainGoal) fvarId
      replaceMainGoal [mvarId]

@[builtin_tactic Lean.Parser.Tactic.subst] def evalSubst : Tactic := fun stx =>
  match stx with
  | `(tactic| subst $hs*) => forEachVar hs Meta.subst
  | _                     => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.substVars] def evalSubstVars : Tactic := fun _ =>
  liftMetaTactic fun mvarId => return [← substVars mvarId]

@[builtin_tactic Lean.Parser.Tactic.substEqs] def evalSubstEqs : Tactic := fun _ =>
  Elab.Tactic.liftMetaTactic1 (·.substEqs)

/--
  Searches for a metavariable `g` s.t. `tag` is its exact name.
  If none then searches for a metavariable `g` s.t. `tag` is a suffix of its name.
  If none, then it searches for a metavariable `g` s.t. `tag` is a prefix of its name. -/
private def findTag? (mvarIds : List MVarId) (tag : Name) : TacticM (Option MVarId) := do
  match (← mvarIds.findM? fun mvarId => return tag == (← mvarId.getDecl).userName) with
  | some mvarId => return mvarId
  | none =>
  match (← mvarIds.findM? fun mvarId => return tag.isSuffixOf (← mvarId.getDecl).userName) with
  | some mvarId => return mvarId
  | none => mvarIds.findM? fun mvarId => return tag.isPrefixOf (← mvarId.getDecl).userName

def renameInaccessibles (mvarId : MVarId) (hs : TSyntaxArray ``binderIdent) : TacticM MVarId := do
  if hs.isEmpty then
    return mvarId
  else
    let mvarDecl ← mvarId.getDecl
    let mut lctx  := mvarDecl.lctx
    let mut hs    := hs
    let mut info  := #[]
    let mut found : NameSet := {}
    let n := lctx.numIndices
    -- hypotheses are inaccessible if their scopes are different from the caller's (we assume that
    -- the scopes are the same for all the hypotheses in `hs`, which is reasonable to expect in
    -- practice and otherwise the expected semantics of `rename_i` really are not clear)
    let some callerScopes := hs.findSome? (fun
        | `(binderIdent| $h:ident) => some <| extractMacroScopes h.getId
        | _ => none)
      | return mvarId
    for i in [:n] do
      let j := n - i - 1
      match lctx.getAt? j with
      | none => pure ()
      | some localDecl =>
        if localDecl.isImplementationDetail then
          continue
        let inaccessible := !(extractMacroScopes localDecl.userName |>.equalScope callerScopes)
        let shadowed := found.contains localDecl.userName
        if inaccessible || shadowed then
          if let `(binderIdent| $h:ident) := hs.back! then
            let newName := h.getId
            lctx := lctx.setUserName localDecl.fvarId newName
            info := info.push (localDecl.fvarId, h)
          hs := hs.pop
          if hs.isEmpty then
            break
        found := found.insert localDecl.userName
    unless hs.isEmpty do
      logError m!"too many variable names provided"
    let mvarNew ← mkFreshExprMVarAt lctx mvarDecl.localInstances mvarDecl.type MetavarKind.syntheticOpaque mvarDecl.userName
    withSaveInfoContext <| mvarNew.mvarId!.withContext do
      for (fvarId, stx) in info do
        Term.addLocalVarInfo stx (mkFVar fvarId)
    mvarId.assign mvarNew
    return mvarNew.mvarId!

private def getCaseGoals (tag : TSyntax ``binderIdent) : TacticM (MVarId × List MVarId) := do
  let gs ← getUnsolvedGoals
  let g ← if let `(binderIdent| $tag:ident) := tag then
    let tag := tag.getId.eraseMacroScopes
    let some g ← findTag? gs tag | notFound gs tag
    pure g
  else
    getMainGoal
  return (g, gs.erase g)

where
  -- When the case tag is not found, construct a message that tells
  -- the user what they could have written
  notFound (available : List MVarId) (tag : Name) := do
    let firstLine := m!"Case tag {showTagName tag} not found."
    -- We must filter out the anonymous name because there may be an
    -- anonymous goal, but users shouldn't be mistakenly encouraged
    -- to write `case anonymous`
    match (← available.mapM getUserName).filter (· ≠ Name.anonymous) with
    | [] =>
      throwError "{firstLine}\n\nThere are no cases to select."
    | [availableName] =>
      throwError "{firstLine}\n\nThe only available case tag is {showTagName availableName}."
    | availableNames =>
      throwError "Case tag {showTagName tag} not found.\n\nAvailable tags:{commaList <| availableNames.map showTagName}"

  getUserName (mv : MVarId) := do return (← mv.getDecl).userName

  showTagName (tagName : Name) : MessageData := m!"'{tagName}'"

  -- Construct a comma-separated list that renders one per line,
  -- indented, if it's too long
  commaList (items : List MessageData) : MessageData :=
    let sep := MessageData.ofFormat "," ++ Format.line
    .group <| .nest 2 <|
    .ofFormat .line ++ .joinSep items sep

@[builtin_tactic «case», builtin_incremental]
def evalCase : Tactic
  | stx@`(tactic| case%$caseTk $[$tag $hs*]|* =>%$arr $tac:tacticSeq1Indented) =>
    -- disable incrementality if body is run multiple times
    Term.withoutTacticIncrementality (tag.size > 1) do
      for tag in tag, hs in hs do
        let (g, gs) ← getCaseGoals tag
        let g ← renameInaccessibles g hs
        setGoals [g]
        g.setTag Name.anonymous
        withCaseRef arr tac <| closeUsingOrAdmit <| withTacticInfoContext (mkNullNode #[caseTk, arr]) <|
          Term.withNarrowedArgTacticReuse (argIdx := 3) (evalTactic ·) stx
        setGoals gs
  | _ => throwUnsupportedSyntax

@[builtin_tactic «case'»] def evalCase' : Tactic
  | `(tactic| case'%$caseTk $[$tag $hs*]|* =>%$arr $tac:tacticSeq) => do
    let mut acc := #[]
    for tag in tag, hs in hs do
      let (g, gs) ← getCaseGoals tag
      let g ← renameInaccessibles g hs
      let mvarTag ← g.getTag
      setGoals [g]
      withCaseRef arr tac <| withTacticInfoContext (mkNullNode #[caseTk, arr]) <| evalTactic tac
      let gs' ← getUnsolvedGoals
      if let [g'] := gs' then
        g'.setTag mvarTag
      acc := acc ++ gs'
      setGoals gs
    setGoals (acc.toList ++ (← getGoals))
  | _ => throwUnsupportedSyntax

@[builtin_tactic «renameI»] def evalRenameInaccessibles : Tactic
  | `(tactic| rename_i $hs*) => do replaceMainGoal [← renameInaccessibles (← getMainGoal) hs]
  | _ => throwUnsupportedSyntax

@[builtin_tactic «first»] partial def evalFirst : Tactic := fun stx => do
  let tacs := stx[1].getArgs
  if tacs.isEmpty then throwUnsupportedSyntax
  loop tacs 0
where
  loop (tacs : Array Syntax) (i : Nat) :=
    if i == tacs.size - 1 then
      evalTactic tacs[i]![1]
    else
      evalTactic tacs[i]![1] <|> loop tacs (i+1)

@[builtin_tactic «fail»] def evalFail : Tactic := fun stx => do
  let goals ← getGoals
  let goalsMsg := MessageData.joinSep (goals.map MessageData.ofGoal) m!"\n\n"
  match stx with
  | `(tactic| fail)          => throwError "tactic 'fail' failed\n{goalsMsg}"
  | `(tactic| fail $msg:str) => throwError "{msg.getString}\n{goalsMsg}"
  | _ => throwUnsupportedSyntax

@[builtin_tactic Parser.Tactic.dbgTrace] def evalDbgTrace : Tactic := fun stx => do
  match stx[1].isStrLit? with
  | none     => throwIllFormedSyntax
  | some msg => dbg_trace msg

@[builtin_tactic sleep] def evalSleep : Tactic := fun stx => do
  match stx[1].isNatLit? with
  | none    => throwIllFormedSyntax
  | some ms => IO.sleep ms.toUInt32

@[builtin_tactic left] def evalLeft : Tactic := fun _stx => do
  liftMetaTactic (fun g => g.nthConstructor `left 0 (some 2))

@[builtin_tactic right] def evalRight : Tactic := fun _stx => do
  liftMetaTactic (fun g => g.nthConstructor `right 1 (some 2))

@[builtin_tactic replace] def evalReplace : Tactic := fun stx => do
  match stx with
  | `(tactic| replace $decl:haveDecl) =>
    withMainContext do
      let vars ← Elab.Term.Do.getDoHaveVars (← `(doElem| have $decl:haveDecl))
      let origLCtx ← getLCtx
      evalTactic $ ← `(tactic| have $decl:haveDecl)
      let mut toClear := #[]
      for fv in vars do
        if let some ldecl := origLCtx.findFromUserName? fv.getId then
          toClear := toClear.push ldecl.fvarId
      liftMetaTactic1 (·.tryClearMany toClear)
  | _ => throwUnsupportedSyntax

@[builtin_tactic runTac] def evalRunTac : Tactic := fun stx => do
  match stx with
  | `(tactic| run_tac $e:doSeq) =>
    ← unsafe Term.evalTerm (TacticM Unit) (mkApp (Lean.mkConst ``TacticM) (Lean.mkConst ``Unit))
      (← `(discard do $e))
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic
