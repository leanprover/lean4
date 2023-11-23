/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Assumption
import Lean.Meta.Tactic.Contradiction
import Lean.Meta.Tactic.Refl
import Lean.Elab.Binders
import Lean.Elab.Open
import Lean.Elab.SetOption
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.ElabTerm

namespace Lean.Elab.Tactic
open Meta
open Parser.Tactic

@[builtin_tactic withAnnotateState] def evalWithAnnotateState : Tactic
  | `(tactic| with_annotate_state $stx $t) =>
    withTacticInfoContext stx (evalTactic t)
  | _ => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.«done»] def evalDone : Tactic := fun _ =>
  done

@[builtin_tactic seq1] def evalSeq1 : Tactic := fun stx => do
  let args := stx[0].getArgs
  for i in [:args.size] do
    if i % 2 == 0 then
      evalTactic args[i]!
    else
      saveTacticInfoForToken args[i]! -- add `TacticInfo` node for `;`

@[builtin_tactic paren] def evalParen : Tactic := fun stx =>
  evalTactic stx[1]

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

/-- Evaluate `sepByIndent tactic "; " -/
def evalSepByIndentTactic (stx : Syntax) : TacticM Unit := do
  let stx ← addCheckpoints stx
  for arg in stx.getArgs, i in [:stx.getArgs.size] do
    if i % 2 == 0 then
      evalTactic arg
    else
      saveTacticInfoForToken arg

@[builtin_tactic tacticSeq1Indented] def evalTacticSeq1Indented : Tactic := fun stx =>
  evalSepByIndentTactic stx[0]

@[builtin_tactic tacticSeqBracketed] def evalTacticSeqBracketed : Tactic := fun stx => do
  let initInfo ← mkInitialTacticInfo stx[0]
  withRef stx[2] <| closeUsingOrAdmit do
    -- save state before/after entering focus on `{`
    withInfoContext (pure ()) initInfo
    evalSepByIndentTactic stx[1]

@[builtin_tactic cdot] def evalTacticCDot : Tactic := fun stx => do
  -- adjusted copy of `evalTacticSeqBracketed`; we used to use the macro
  -- ``| `(tactic| $cdot:cdotTk $tacs) => `(tactic| {%$cdot ($tacs) }%$cdot)``
  -- but the token antiquotation does not copy trailing whitespace, leading to
  -- differences in the goal display (#2153)
  let initInfo ← mkInitialTacticInfo stx[0]
  withRef stx[0] <| closeUsingOrAdmit do
    -- save state before/after entering focus on `·`
    withInfoContext (pure ()) initInfo
    evalSepByIndentTactic stx[1]

@[builtin_tactic Parser.Tactic.focus] def evalFocus : Tactic := fun stx => do
  let mkInfo ← mkInitialTacticInfo stx[0]
  focus do
    -- show focused state on `focus`
    withInfoContext (pure ()) mkInfo
    evalTactic stx[1]

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
  let options ← Elab.elabSetOption stx[1] stx[2]
  withTheReader Core.Context (fun ctx => { ctx with maxRecDepth := maxRecDepth.get options, options := options }) do
    evalTactic stx[4]

@[builtin_tactic Parser.Tactic.allGoals] def evalAllGoals : Tactic := fun stx => do
  let mvarIds ← getGoals
  let mut mvarIdsNew := #[]
  for mvarId in mvarIds do
    unless (← mvarId.isAssigned) do
      setGoals [mvarId]
      try
        evalTactic stx[1]
        mvarIdsNew := mvarIdsNew ++ (← getUnsolvedGoals)
      catch ex =>
        if (← read).recover then
          logException ex
          mvarIdsNew := mvarIdsNew.push mvarId
        else
          throw ex
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

@[builtin_tactic tacticSeq] def evalTacticSeq : Tactic := fun stx =>
  evalTactic stx[0]

partial def evalChoiceAux (tactics : Array Syntax) (i : Nat) : TacticM Unit :=
  if h : i < tactics.size then
    let tactic := tactics.get ⟨i, h⟩
    catchInternalId unsupportedSyntaxExceptionId
      (evalTactic tactic)
      (fun _ => evalChoiceAux tactics (i+1))
  else
    throwUnsupportedSyntax

@[builtin_tactic choice] def evalChoice : Tactic := fun stx =>
  evalChoiceAux stx.getArgs 0

@[builtin_tactic skip] def evalSkip : Tactic := fun _ => pure ()

@[builtin_tactic unknown] def evalUnknown : Tactic := fun stx => do
  addCompletionInfo <| CompletionInfo.tactic stx (← getGoals)

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
        let type ← Term.withSynthesize (mayPostpone := true) <| Term.elabType typeStx
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
    for i in [:n] do
      let j := n - i - 1
      match lctx.getAt? j with
      | none => pure ()
      | some localDecl =>
        if localDecl.userName.hasMacroScopes || found.contains localDecl.userName then
          if let `(binderIdent| $h:ident) := hs.back then
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
    let tag := tag.getId
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


@[builtin_tactic «case»] def evalCase : Tactic
  | stx@`(tactic| case $[$tag $hs*]|* =>%$arr $tac:tacticSeq) =>
    for tag in tag, hs in hs do
      let (g, gs) ← getCaseGoals tag
      let g ← renameInaccessibles g hs
      setGoals [g]
      g.setTag Name.anonymous
      withCaseRef arr tac do
        closeUsingOrAdmit (withTacticInfoContext stx (evalTactic tac))
      setGoals gs
  | _ => throwUnsupportedSyntax

@[builtin_tactic «case'»] def evalCase' : Tactic
  | `(tactic| case' $[$tag $hs*]|* =>%$arr $tac:tacticSeq) => do
    let mut acc := #[]
    for tag in tag, hs in hs do
      let (g, gs) ← getCaseGoals tag
      let g ← renameInaccessibles g hs
      let mvarTag ← g.getTag
      setGoals [g]
      withCaseRef arr tac (evalTactic tac)
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

end Lean.Elab.Tactic
