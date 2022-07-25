/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Refl
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.ElabTerm

namespace Lean.Elab.Tactic
open Meta
open Parser.Tactic

@[builtinTactic withAnnotateState] def evalWithAnnotateState : Tactic
  | `(tactic| with_annotate_state $stx $t) =>
    withTacticInfoContext stx (evalTactic t)
  | _ => throwUnsupportedSyntax

@[builtinTactic Lean.Parser.Tactic.«done»] def evalDone : Tactic := fun _ =>
  done

@[builtinTactic seq1] def evalSeq1 : Tactic := fun stx => do
  let args := stx[0].getArgs
  for i in [:args.size] do
    if i % 2 == 0 then
      evalTactic args[i]!
    else
      saveTacticInfoForToken args[i]! -- add `TacticInfo` node for `;`

@[builtinTactic paren] def evalParen : Tactic := fun stx =>
  evalTactic stx[1]

def isCheckpointableTactic (arg : Syntax) : TacticM Bool := do
  -- TODO: make it parametric
  let kind := arg.getKind
  return kind == ``Lean.Parser.Tactic.save

partial def addCheckpoints (args : Array Syntax) : TacticM (Array Syntax) := do
  -- if (← readThe Term.Context).tacticCache? |>.isSome then
  if (← args.anyM fun arg => isCheckpointableTactic arg[0]) then
    let argsNew ← go 0 #[] #[]
    return argsNew
  return args
where
  push (acc : Array Syntax) (result : Array Syntax) : Array Syntax :=
    if acc.isEmpty then
      result
    else
      let ref := acc.back
      let accSeq := mkNode ``Lean.Parser.Tactic.tacticSeq1Indented #[mkNullNode acc]
      let checkpoint := mkNode ``Lean.Parser.Tactic.checkpoint #[mkAtomFrom ref "checkpoint", accSeq]
      result.push (mkNode groupKind #[checkpoint, mkNullNode])

  go (i : Nat) (acc : Array Syntax) (result : Array Syntax) : TacticM (Array Syntax) := do
    if h : i < args.size then
      let arg := args.get ⟨i, h⟩
      if (← isCheckpointableTactic arg[0]) then
        -- `argNew` is `arg` as singleton sequence. The idea is to make sure it does not satisfy `isCheckpointableTactic` anymore
        let argNew := arg.setArg 0 (mkNullNode #[arg[0]])
        let acc := acc.push argNew
        go (i+1) #[] (push acc result)
      else
        go (i+1) (acc.push arg) result
    else
      return result ++ acc

/-- Evaluate `many (group (tactic >> optional ";")) -/
def evalManyTacticOptSemi (stx : Syntax) : TacticM Unit := do
  for seqElem in (← addCheckpoints stx.getArgs) do
    evalTactic seqElem[0]
    saveTacticInfoForToken seqElem[1] -- add TacticInfo node for `;`

@[builtinTactic tacticSeq1Indented] def evalTacticSeq1Indented : Tactic := fun stx =>
  evalManyTacticOptSemi stx[0]

@[builtinTactic tacticSeqBracketed] def evalTacticSeqBracketed : Tactic := fun stx => do
  let initInfo ← mkInitialTacticInfo stx[0]
  withRef stx[2] <| closeUsingOrAdmit do
    -- save state before/after entering focus on `{`
    withInfoContext (pure ()) initInfo
    evalManyTacticOptSemi stx[1]

@[builtinTactic Parser.Tactic.focus] def evalFocus : Tactic := fun stx => do
  let mkInfo ← mkInitialTacticInfo stx[0]
  focus do
    -- show focused state on `focus`
    withInfoContext (pure ()) mkInfo
    evalTactic stx[1]

private def getOptRotation (stx : Syntax) : Nat :=
  if stx.isNone then 1 else stx[0].toNat

@[builtinTactic Parser.Tactic.rotateLeft] def evalRotateLeft : Tactic := fun stx => do
  let n := getOptRotation stx[1]
  setGoals <| (← getGoals).rotateLeft n

@[builtinTactic Parser.Tactic.rotateRight] def evalRotateRight : Tactic := fun stx => do
  let n := getOptRotation stx[1]
  setGoals <| (← getGoals).rotateRight n

@[builtinTactic Parser.Tactic.open] def evalOpen : Tactic := fun stx => do
  try
    pushScope
    let openDecls ← elabOpenDecl stx[1]
    withTheReader Core.Context (fun ctx => { ctx with openDecls := openDecls }) do
      evalTactic stx[3]
  finally
    popScope

@[builtinTactic Parser.Tactic.set_option] def elabSetOption : Tactic := fun stx => do
  let options ← Elab.elabSetOption stx[1] stx[2]
  withTheReader Core.Context (fun ctx => { ctx with maxRecDepth := maxRecDepth.get options, options := options }) do
    evalTactic stx[4]

@[builtinTactic Parser.Tactic.allGoals] def evalAllGoals : Tactic := fun stx => do
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

@[builtinTactic Parser.Tactic.anyGoals] def evalAnyGoals : Tactic := fun stx => do
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

@[builtinTactic tacticSeq] def evalTacticSeq : Tactic := fun stx =>
  evalTactic stx[0]

partial def evalChoiceAux (tactics : Array Syntax) (i : Nat) : TacticM Unit :=
  if h : i < tactics.size then
    let tactic := tactics.get ⟨i, h⟩
    catchInternalId unsupportedSyntaxExceptionId
      (evalTactic tactic)
      (fun _ => evalChoiceAux tactics (i+1))
  else
    throwUnsupportedSyntax

@[builtinTactic choice] def evalChoice : Tactic := fun stx =>
  evalChoiceAux stx.getArgs 0

@[builtinTactic skip] def evalSkip : Tactic := fun _ => pure ()

@[builtinTactic unknown] def evalUnknown : Tactic := fun stx => do
  addCompletionInfo <| CompletionInfo.tactic stx (← getGoals)

@[builtinTactic failIfSuccess] def evalFailIfSuccess : Tactic := fun stx => do
  let tactic := stx[1]
  if (← try evalTactic tactic; pure true catch _ => pure false) then
    throwError "tactic succeeded"

@[builtinTactic traceState] def evalTraceState : Tactic := fun _ => do
  let gs ← getUnsolvedGoals
  addRawTrace (goalsToMessageData gs)

@[builtinTactic traceMessage] def evalTraceMessage : Tactic := fun stx => do
  match stx[1].isStrLit? with
  | none     => throwIllFormedSyntax
  | some msg => withRef stx[0] <| addRawTrace msg

@[builtinTactic Lean.Parser.Tactic.assumption] def evalAssumption : Tactic := fun _ =>
  liftMetaTactic fun mvarId => do mvarId.assumption; pure []

@[builtinTactic Lean.Parser.Tactic.contradiction] def evalContradiction : Tactic := fun _ =>
  liftMetaTactic fun mvarId => do Meta.contradiction mvarId; pure []

@[builtinTactic Lean.Parser.Tactic.refl] def evalRefl : Tactic := fun _ =>
  liftMetaTactic fun mvarId => do mvarId.refl; pure []

@[builtinTactic Lean.Parser.Tactic.intro] def evalIntro : Tactic := fun stx => do
  match stx with
  | `(tactic| intro)                   => introStep none `_
  | `(tactic| intro $h:ident)          => introStep h h.getId
  | `(tactic| intro _%$tk)             => introStep tk `_
  | `(tactic| intro $pat:term)         => evalTactic (← `(tactic| intro h; match h with | $pat:term => ?_; try clear h))
  | `(tactic| intro $h:term $hs:term*) => evalTactic (← `(tactic| intro $h:term; intro $hs:term*))
  | _ => throwUnsupportedSyntax
where
  introStep (ref : Option Syntax) (n : Name) : TacticM Unit := do
    let fvar ← liftMetaTacticAux fun mvarId => do
      let (fvar, mvarId) ← mvarId.intro n
      pure (fvar, [mvarId])
    if let some stx := ref then
      withMainContext do
        Term.addLocalVarInfo stx (mkFVar fvar)

@[builtinTactic Lean.Parser.Tactic.introMatch] def evalIntroMatch : Tactic := fun stx => do
  let matchAlts := stx[1]
  let stxNew ← liftMacroM <| Term.expandMatchAltsIntoMatchTactic stx matchAlts
  withMacroExpansion stx stxNew <| evalTactic stxNew

@[builtinTactic «intros»] def evalIntros : Tactic := fun stx =>
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

@[builtinTactic Lean.Parser.Tactic.revert] def evalRevert : Tactic := fun stx =>
  match stx with
  | `(tactic| revert $hs*) => do
     let (_, mvarId) ← (← getMainGoal).revert (← getFVarIds hs)
     replaceMainGoal [mvarId]
  | _                     => throwUnsupportedSyntax

@[builtinTactic Lean.Parser.Tactic.clear] def evalClear : Tactic := fun stx =>
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

@[builtinTactic Lean.Parser.Tactic.subst] def evalSubst : Tactic := fun stx =>
  match stx with
  | `(tactic| subst $hs*) => forEachVar hs Meta.subst
  | _                     => throwUnsupportedSyntax

@[builtinTactic Lean.Parser.Tactic.substVars] def evalSubstVars : Tactic := fun _ =>
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
    let some g ← findTag? gs tag | throwError "tag not found"
    pure g
  else
    getMainGoal
  return (g, gs.erase g)

@[builtinTactic «case»] def evalCase : Tactic
  | stx@`(tactic| case $tag $hs* =>%$arr $tac:tacticSeq) => do
    let (g, gs) ← getCaseGoals tag
    let g ← renameInaccessibles g hs
    setGoals [g]
    g.setTag Name.anonymous
    withCaseRef arr tac do
      closeUsingOrAdmit (withTacticInfoContext stx (evalTactic tac))
    setGoals gs
  | _ => throwUnsupportedSyntax

@[builtinTactic «case'»] def evalCase' : Tactic
  | `(tactic| case' $tag $hs* =>%$arr $tac:tacticSeq) => do
    let (g, gs) ← getCaseGoals tag
    let g ← renameInaccessibles g hs
    let mvarTag ← g.getTag
    setGoals [g]
    withCaseRef arr tac (evalTactic tac)
    let gs' ← getUnsolvedGoals
    if let [g'] := gs' then
      g'.setTag mvarTag
    setGoals (gs' ++ gs)
  | _ => throwUnsupportedSyntax

@[builtinTactic «renameI»] def evalRenameInaccessibles : Tactic
  | `(tactic| rename_i $hs*) => do replaceMainGoal [← renameInaccessibles (← getMainGoal) hs]
  | _ => throwUnsupportedSyntax

@[builtinTactic «first»] partial def evalFirst : Tactic := fun stx => do
  let tacs := stx[1].getArgs
  if tacs.isEmpty then throwUnsupportedSyntax
  loop tacs 0
where
  loop (tacs : Array Syntax) (i : Nat) :=
    if i == tacs.size - 1 then
      evalTactic tacs[i]![1]
    else
      evalTactic tacs[i]![1] <|> loop tacs (i+1)

@[builtinTactic «fail»] def evalFail : Tactic := fun stx => do
  let goals ← getGoals
  let goalsMsg := MessageData.joinSep (goals.map MessageData.ofGoal) m!"\n\n"
  match stx with
  | `(tactic| fail)          => throwError "tactic 'fail' failed\n{goalsMsg}"
  | `(tactic| fail $msg:str) => throwError "{msg.getString}\n{goalsMsg}"
  | _ => throwUnsupportedSyntax

@[builtinTactic dbgTrace] def evalDbgTrace : Tactic := fun stx => do
  match stx[1].isStrLit? with
  | none     => throwIllFormedSyntax
  | some msg => dbg_trace msg

@[builtinTactic sleep] def evalSleep : Tactic := fun stx => do
  match stx[1].isNatLit? with
  | none    => throwIllFormedSyntax
  | some ms => IO.sleep ms.toUInt32

end Lean.Elab.Tactic
