/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Tactic.Basic

namespace Lean.Elab.Tactic
open Meta

@[builtinTactic Lean.Parser.Tactic.«done»] def evalDone : Tactic := fun _ =>
  done

@[builtinTactic seq1] def evalSeq1 : Tactic := fun stx => do
  let args := stx[0].getArgs
  for i in [:args.size] do
    if i % 2 == 0 then
      evalTactic args[i]
    else
      saveTacticInfoForToken args[i] -- add `TacticInfo` node for `;`

@[builtinTactic paren] def evalParen : Tactic := fun stx =>
  evalTactic stx[1]

/- Evaluate `many (group (tactic >> optional ";")) -/
private def evalManyTacticOptSemi (stx : Syntax) : TacticM Unit := do
  stx.forArgsM fun seqElem => do
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
    unless (← isExprMVarAssigned mvarId) do
      setGoals [mvarId]
      try
        evalTactic stx[1]
        mvarIdsNew := mvarIdsNew ++ (← getUnsolvedGoals)
      catch ex =>
        logException ex
        mvarIdsNew := mvarIdsNew.push mvarId
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

@[builtinTactic skip] def evalSkip : Tactic := fun stx => pure ()

@[builtinTactic unknown] def evalUnknown : Tactic := fun stx => do
  addCompletionInfo <| CompletionInfo.tactic stx (← getGoals)

@[builtinTactic failIfSuccess] def evalFailIfSuccess : Tactic := fun stx => do
  let tactic := stx[1]
  if (← try evalTactic tactic; pure true catch _ => pure false) then
    throwError "tactic succeeded"

@[builtinTactic traceState] def evalTraceState : Tactic := fun stx => do
  let gs ← getUnsolvedGoals
  logInfo (goalsToMessageData gs)

@[builtinTactic Lean.Parser.Tactic.assumption] def evalAssumption : Tactic := fun stx =>
  liftMetaTactic fun mvarId => do Meta.assumption mvarId; pure []

@[builtinTactic Lean.Parser.Tactic.contradiction] def evalContradiction : Tactic := fun stx =>
  liftMetaTactic fun mvarId => do Meta.contradiction mvarId; pure []

@[builtinTactic Lean.Parser.Tactic.intro] def evalIntro : Tactic := fun stx => do
  match stx with
  | `(tactic| intro)                   => introStep `_
  | `(tactic| intro $h:ident)          => introStep h.getId
  | `(tactic| intro _)                 => introStep `_
  | `(tactic| intro $pat:term)         => evalTactic (← `(tactic| intro h; match h with | $pat:term => ?_; try clear h))
  | `(tactic| intro $h:term $hs:term*) => evalTactic (← `(tactic| intro $h:term; intro $hs:term*))
  | _ => throwUnsupportedSyntax
where
  introStep (n : Name) : TacticM Unit :=
    liftMetaTactic fun mvarId => do
      let (_, mvarId) ← Meta.intro mvarId n
      pure [mvarId]

@[builtinTactic Lean.Parser.Tactic.introMatch] def evalIntroMatch : Tactic := fun stx => do
  let matchAlts := stx[1]
  let stxNew ← liftMacroM <| Term.expandMatchAltsIntoMatchTactic stx matchAlts
  withMacroExpansion stx stxNew <| evalTactic stxNew

private def getIntrosSize : Expr → Nat
  | Expr.forallE _ _ b _ => getIntrosSize b + 1
  | Expr.letE _ _ _ b _  => getIntrosSize b + 1
  | Expr.mdata _ b _     => getIntrosSize b
  | _                    => 0

@[builtinTactic «intros»] def evalIntros : Tactic := fun stx =>
  match stx with
  | `(tactic| intros) => liftMetaTactic fun mvarId => do
    let type ← Meta.getMVarType mvarId
    let type ← instantiateMVars type
    let n := getIntrosSize type
    let (_, mvarId) ← Meta.introN mvarId n
    pure [mvarId]
  | `(tactic| intros $ids*) => liftMetaTactic fun mvarId => do
    let (_, mvarId) ← Meta.introN mvarId ids.size (ids.map getNameOfIdent').toList
    pure [mvarId]
  | _ => throwUnsupportedSyntax

@[builtinTactic Lean.Parser.Tactic.revert] def evalRevert : Tactic := fun stx =>
  match stx with
  | `(tactic| revert $hs*) => do
     let (_, mvarId) ← Meta.revert (← getMainGoal) (← getFVarIds hs)
     replaceMainGoal [mvarId]
  | _                     => throwUnsupportedSyntax

/- Sort free variables using an order `x < y` iff `x` was defined after `y` -/
private def sortFVarIds (fvarIds : Array FVarId) : TacticM (Array FVarId) :=
  withMainContext do
    let lctx ← getLCtx
    return fvarIds.qsort fun fvarId₁ fvarId₂ =>
      match lctx.find? fvarId₁, lctx.find? fvarId₂ with
      | some d₁, some d₂ => d₁.index > d₂.index
      | some _,  none    => false
      | none,    some _  => true
      | none,    none    => Name.quickLt fvarId₁ fvarId₂

@[builtinTactic Lean.Parser.Tactic.clear] def evalClear : Tactic := fun stx =>
  match stx with
  | `(tactic| clear $hs*) => do
    let fvarIds ← getFVarIds hs
    let fvarIds ← sortFVarIds fvarIds
    for fvarId in fvarIds do
      withMainContext do
        let mvarId ← clear (← getMainGoal) fvarId
        replaceMainGoal [mvarId]
  | _ => throwUnsupportedSyntax

def forEachVar (hs : Array Syntax) (tac : MVarId → FVarId → MetaM MVarId) : TacticM Unit := do
  for h in hs do
    withMainContext do
      let fvarId ← getFVarId h
      let mvarId ← tac (← getMainGoal) (← getFVarId h)
      replaceMainGoal [mvarId]

@[builtinTactic Lean.Parser.Tactic.subst] def evalSubst : Tactic := fun stx =>
  match stx with
  | `(tactic| subst $hs*) => forEachVar hs Meta.subst
  | _                     => throwUnsupportedSyntax

/--
  First method searches for a metavariable `g` s.t. `tag` is a suffix of its name.
  If none is found, then it searches for a metavariable `g` s.t. `tag` is a prefix of its name. -/
private def findTag? (mvarIds : List MVarId) (tag : Name) : TacticM (Option MVarId) := do
  let mvarId? ← mvarIds.findM? fun mvarId => return tag.isSuffixOf (← getMVarDecl mvarId).userName
  match mvarId? with
  | some mvarId => return mvarId
  | none        => mvarIds.findM? fun mvarId => return tag.isPrefixOf (← getMVarDecl mvarId).userName

@[builtinTactic «case»] def evalCase : Tactic
  | stx@`(tactic| case $tag $hs* =>%$arr $tac:tacticSeq) => do
    let tag := tag.getId
    let gs ← getUnsolvedGoals
    let some g ← findTag? gs tag | throwError "tag not found"
    let gs := gs.erase g
    let mut g := g
    unless hs.isEmpty do
      let mvarDecl ← getMVarDecl g
      let mut lctx := mvarDecl.lctx
      let mut hs   := hs
      let n := lctx.numIndices
      for i in [:n] do
        let j := n - i - 1
        match lctx.getAt? j with
        | none => pure ()
        | some localDecl =>
          if localDecl.userName.hasMacroScopes then
            let h := hs.back
            if h.isIdent then
              let newName := h.getId
              lctx := lctx.setUserName localDecl.fvarId newName
            hs := hs.pop
            if hs.isEmpty then
              break
      unless hs.isEmpty do
        logError m!"too many variable names provided at 'case'"
      let mvarNew ← mkFreshExprMVarAt lctx mvarDecl.localInstances mvarDecl.type MetavarKind.syntheticOpaque mvarDecl.userName
      assignExprMVar g mvarNew
      g := mvarNew.mvarId!
    setGoals [g]
    let savedTag ← getMVarTag g
    setMVarTag g Name.anonymous
    try
      withCaseRef arr tac do
        closeUsingOrAdmit (withTacticInfoContext stx (evalTactic tac))
    finally
      setMVarTag g savedTag
    done
    setGoals gs
  | _ => throwUnsupportedSyntax

@[builtinTactic «first»] partial def evalFirst : Tactic := fun stx => do
  let tacs := stx[1].getArgs
  if tacs.isEmpty then throwUnsupportedSyntax
  loop tacs 0
where
  loop (tacs : Array Syntax) (i : Nat) :=
    if i == tacs.size - 1 then
      evalTactic tacs[i][1]
    else
      evalTactic tacs[i][1] <|> loop tacs (i+1)

end Lean.Elab.Tactic
