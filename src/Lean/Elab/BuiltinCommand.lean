/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Util.CollectLevelParams
import Lean.Util.CollectAxioms
import Lean.Meta.Reduce
import Lean.Elab.DeclarationRange
import Lean.Elab.Eval
import Lean.Elab.Command
import Lean.Elab.Open
import Lean.Elab.SetOption

namespace Lean.Elab.Command

@[builtin_command_elab moduleDoc] def elabModuleDoc : CommandElab := fun stx => do
   match stx[1] with
   | Syntax.atom _ val =>
     let doc := val.extract 0 (val.endPos - ⟨2⟩)
     let range ← Elab.getDeclarationRange stx
     modifyEnv fun env => addMainModuleDoc env ⟨doc, range⟩
   | _ => throwErrorAt stx "unexpected module doc string{indentD stx[1]}"

private def addScope (isNewNamespace : Bool) (isNoncomputable : Bool) (header : String) (newNamespace : Name) : CommandElabM Unit := do
  modify fun s => { s with
    env    := s.env.registerNamespace newNamespace,
    scopes := { s.scopes.head! with header := header, currNamespace := newNamespace, isNoncomputable := s.scopes.head!.isNoncomputable || isNoncomputable } :: s.scopes
  }
  pushScope
  if isNewNamespace then
    activateScoped newNamespace

private def addScopes (isNewNamespace : Bool) (isNoncomputable : Bool) : Name → CommandElabM Unit
  | .anonymous => pure ()
  | .str p header => do
    addScopes isNewNamespace isNoncomputable p
    let currNamespace ← getCurrNamespace
    addScope isNewNamespace isNoncomputable header (if isNewNamespace then Name.mkStr currNamespace header else currNamespace)
  | _ => throwError "invalid scope"

private def addNamespace (header : Name) : CommandElabM Unit :=
  addScopes (isNewNamespace := true) (isNoncomputable := false) header

def withNamespace {α} (ns : Name) (elabFn : CommandElabM α) : CommandElabM α := do
  addNamespace ns
  let a ← elabFn
  modify fun s => { s with scopes := s.scopes.drop ns.getNumParts }
  pure a

private def popScopes (numScopes : Nat) : CommandElabM Unit :=
  for _ in [0:numScopes] do
    popScope

private def checkAnonymousScope : List Scope → Option Name
  | { header := "", .. } :: _ => none
  | { header := h, .. }  :: _ => some <| .mkSimple h
  | _                         => some .anonymous -- should not happen

private def checkEndHeader : Name → List Scope → Option Name
  | .anonymous, _ => none
  | .str p s, { header := h, .. } :: scopes =>
    if h == s then
      (.str · s) <$> checkEndHeader p scopes
    else
      some <| .mkSimple h
  | _, _ => some .anonymous -- should not happen

@[builtin_command_elab «namespace»] def elabNamespace : CommandElab := fun stx =>
  match stx with
  | `(namespace $n) => addNamespace n.getId
  | _               => throwUnsupportedSyntax

@[builtin_command_elab «section»] def elabSection : CommandElab := fun stx => do
  match stx with
  | `(section $header:ident) => addScopes (isNewNamespace := false) (isNoncomputable := false) header.getId
  | `(section)               => addScope (isNewNamespace := false) (isNoncomputable := false) "" (← getCurrNamespace)
  | _                        => throwUnsupportedSyntax

@[builtin_command_elab noncomputableSection] def elabNonComputableSection : CommandElab := fun stx => do
  match stx with
  | `(noncomputable section $header:ident) => addScopes (isNewNamespace := false) (isNoncomputable := true) header.getId
  | `(noncomputable section)               => addScope (isNewNamespace := false) (isNoncomputable := true) "" (← getCurrNamespace)
  | _                        => throwUnsupportedSyntax

@[builtin_command_elab «end»] def elabEnd : CommandElab := fun stx => do
  let header? := (stx.getArg 1).getOptionalIdent?;
  let endSize := match header? with
    | none   => 1
    | some n => n.getNumParts
  let scopes ← getScopes
  if endSize < scopes.length then
    modify fun s => { s with scopes := s.scopes.drop endSize }
    popScopes endSize
  else -- we keep "root" scope
    let n := (← get).scopes.length - 1
    modify fun s => { s with scopes := s.scopes.drop n }
    popScopes n
    throwError "invalid 'end', insufficient scopes"
  match header? with
  | none        =>
    if let some name := checkAnonymousScope scopes then
      throwError "invalid 'end', name is missing (expected {name})"
  | some header =>
    if let some name := checkEndHeader header scopes then
      addCompletionInfo <| CompletionInfo.endSection stx (scopes.map fun scope => scope.header)
      throwError "invalid 'end', name mismatch (expected {if name == `«» then `nothing else name})"

private partial def elabChoiceAux (cmds : Array Syntax) (i : Nat) : CommandElabM Unit :=
  if h : i < cmds.size then
    let cmd := cmds.get ⟨i, h⟩;
    catchInternalId unsupportedSyntaxExceptionId
      (elabCommand cmd)
      (fun _ => elabChoiceAux cmds (i+1))
  else
    throwUnsupportedSyntax

@[builtin_command_elab choice] def elabChoice : CommandElab := fun stx =>
  elabChoiceAux stx.getArgs 0

@[builtin_command_elab «universe»] def elabUniverse : CommandElab := fun n => do
  n[1].forArgsM addUnivLevel

@[builtin_command_elab «init_quot»] def elabInitQuot : CommandElab := fun _ => do
  match (← getEnv).addDecl (← getOptions) Declaration.quotDecl with
  | Except.ok env   => setEnv env
  | Except.error ex => throwError (ex.toMessageData (← getOptions))

@[builtin_command_elab «export»] def elabExport : CommandElab := fun stx => do
  let `(export $ns ($ids*)) := stx | throwUnsupportedSyntax
  let nss ← resolveNamespace ns
  let currNamespace ← getCurrNamespace
  if nss == [currNamespace] then throwError "invalid 'export', self export"
  let mut aliases := #[]
  for idStx in ids do
    let id := idStx.getId
    let declName ← resolveNameUsingNamespaces nss idStx
    if (← getInfoState).enabled then
      addConstInfo idStx declName
    aliases := aliases.push (currNamespace ++ id, declName)
  modify fun s => { s with env := aliases.foldl (init := s.env) fun env p => addAlias env p.1 p.2 }

@[builtin_command_elab «open»] def elabOpen : CommandElab
  | `(open $decl:openDecl) => do
    let openDecls ← elabOpenDecl decl
    modifyScope fun scope => { scope with openDecls := openDecls }
  | _ => throwUnsupportedSyntax

open Lean.Parser.Term

private def typelessBinder? : Syntax → Option (Array (TSyntax [`ident, `Lean.Parser.Term.hole]) × Bool)
  | `(bracketedBinderF|($ids*)) => some (ids, true)
  | `(bracketedBinderF|{$ids*}) => some (ids, false)
  | _                          => none

/--  If `id` is an identifier, return true if `ids` contains `id`. -/
private def containsId (ids : Array (TSyntax [`ident, ``Parser.Term.hole])) (id : TSyntax [`ident, ``Parser.Term.hole]) : Bool :=
  id.raw.isIdent && ids.any fun id' => id'.raw.getId == id.raw.getId

/--
  Auxiliary method for processing binder annotation update commands: `variable (α)` and `variable {α}`.
  The argument `binder` is the binder of the `variable` command.
  The method returns an array containing the "residue", that is, variables that do not correspond to updates.
  Recall that a `bracketedBinder` can be of the form `(x y)`.
  ```
  variable {α β : Type}
  variable (α γ)
  ```
  The second `variable` command updates the binder annotation for `α`, and returns "residue" `γ`.
-/
private def replaceBinderAnnotation (binder : TSyntax ``Parser.Term.bracketedBinder) : CommandElabM (Array (TSyntax ``Parser.Term.bracketedBinder)) := do
  let some (binderIds, explicit) := typelessBinder? binder | return #[binder]
  let varDecls := (← getScope).varDecls
  let mut varDeclsNew := #[]
  let mut binderIds := binderIds
  let mut binderIdsIniSize := binderIds.size
  let mut modifiedVarDecls := false
  -- Go through declarations in reverse to respect shadowing
  for varDecl in varDecls.reverse do
    let (ids, ty?, explicit') ← match varDecl with
      | `(bracketedBinderF|($ids* $[: $ty?]? $(annot?)?)) =>
        if annot?.isSome then
          for binderId in binderIds do
            if containsId ids binderId then
              throwErrorAt binderId "cannot update binder annotation of variables with default values/tactics"
        pure (ids, ty?, true)
      | `(bracketedBinderF|{$ids* $[: $ty?]?}) =>
        pure (ids, ty?, false)
      | `(bracketedBinderF|[$id : $_]) =>
        for binderId in binderIds do
          if binderId.raw.isIdent && binderId.raw.getId == id.getId then
            throwErrorAt binderId "cannot change the binder annotation of the previously declared local instance `{id.getId}`"
        varDeclsNew := varDeclsNew.push varDecl; continue
      | _ =>
        varDeclsNew := varDeclsNew.push varDecl; continue
    if explicit == explicit' then
      -- no update, ensure we don't have redundant annotations.
      for binderId in binderIds do
        if containsId ids binderId then
          throwErrorAt binderId "redundant binder annotation update"
      varDeclsNew := varDeclsNew.push varDecl
    else if binderIds.all fun binderId => !containsId ids binderId then
      -- `binderIds` and `ids` are disjoint
      varDeclsNew := varDeclsNew.push varDecl
    else
      let mkBinder (id : TSyntax [`ident, ``Parser.Term.hole]) (explicit : Bool) : CommandElabM (TSyntax ``Parser.Term.bracketedBinder) :=
        if explicit then
          `(bracketedBinderF| ($id $[: $ty?]?))
        else
          `(bracketedBinderF| {$id $[: $ty?]?})
      for id in ids.reverse do
        if let some idx := binderIds.findIdx? fun binderId => binderId.raw.isIdent && binderId.raw.getId == id.raw.getId then
          binderIds := binderIds.eraseIdx idx
          modifiedVarDecls := true
          varDeclsNew := varDeclsNew.push (← mkBinder id explicit)
        else
          varDeclsNew := varDeclsNew.push (← mkBinder id explicit')
  if modifiedVarDecls then
    modifyScope fun scope => { scope with varDecls := varDeclsNew.reverse }
  if binderIds.size != binderIdsIniSize then
    binderIds.mapM fun binderId =>
      if explicit then
        `(bracketedBinderF| ($binderId))
      else
        `(bracketedBinderF| {$binderId})
  else
    return #[binder]

@[builtin_command_elab «variable»] def elabVariable : CommandElab
  | `(variable $binders*) => do
    let binders ← binders.concatMapM replaceBinderAnnotation
    -- Try to elaborate `binders` for sanity checking
    runTermElabM fun _ => Term.withSynthesize <| Term.withAutoBoundImplicit <|
      Term.elabBinders binders fun _ => pure ()
    -- Remark: if we want to produce error messages when variables shadow existing ones, here is the place to do it.
    for binder in binders do
      let varUIds ← (← getBracketedBinderIds binder) |>.mapM (withFreshMacroScope ∘ MonadQuotation.addMacroScope)
      modifyScope fun scope => { scope with varDecls := scope.varDecls.push binder, varUIds := scope.varUIds ++ varUIds }
  | _ => throwUnsupportedSyntax

open Meta

def elabCheckCore (ignoreStuckTC : Bool) : CommandElab
  | `(#check%$tk $term) => withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_check do
    -- show signature for `#check id`/`#check @id`
    if let `($id:ident) := term then
      try
        for c in (← realizeGlobalConstWithInfos term) do
          addCompletionInfo <| .id term id.getId (danglingDot := false) {} none
          logInfoAt tk <| .signature c
          return
      catch _ => pure ()  -- identifier might not be a constant but constant + projection
    let e ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := ignoreStuckTC)
    -- Users might be testing out buggy elaborators. Let's typecheck before proceeding:
    withRef tk <| Meta.check e
    let e ← Term.levelMVarToParam (← instantiateMVars e)
    if e.isSyntheticSorry then
      return
    let type ← inferType e
    logInfoAt tk m!"{e} : {type}"
  | _ => throwUnsupportedSyntax

@[builtin_command_elab Lean.Parser.Command.check] def elabCheck : CommandElab := elabCheckCore (ignoreStuckTC := true)

@[builtin_command_elab Lean.reduceCmd] def elabReduce : CommandElab
  | `(#reduce%$tk $term) => go tk term
  | `(#reduce%$tk (proofs := true) $term) => go tk term (skipProofs := false)
  | `(#reduce%$tk (types := true) $term) => go tk term (skipTypes := false)
  | `(#reduce%$tk (proofs := true) (types := true) $term) => go tk term (skipProofs := false) (skipTypes := false)
  | _ => throwUnsupportedSyntax
where
  go (tk : Syntax) (term : Syntax) (skipProofs := true) (skipTypes := true) : CommandElabM Unit :=
    withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_reduce do
      let e ← Term.elabTerm term none
      Term.synthesizeSyntheticMVarsNoPostponing
      -- Users might be testing out buggy elaborators. Let's typecheck before proceeding:
      withRef tk <| Meta.check e
      let e ← Term.levelMVarToParam (← instantiateMVars e)
      -- TODO: add options or notation for setting the following parameters
      withTheReader Core.Context (fun ctx => { ctx with options := ctx.options.setBool `smartUnfolding false }) do
        let e ← withTransparency (mode := TransparencyMode.all) <| reduce e (skipProofs := skipProofs) (skipTypes := skipTypes)
        logInfoAt tk e

def hasNoErrorMessages : CommandElabM Bool := do
  return !(← get).messages.hasErrors

def failIfSucceeds (x : CommandElabM Unit) : CommandElabM Unit := do
  let resetMessages : CommandElabM MessageLog := do
    let s ← get
    let messages := s.messages;
    modify fun s => { s with messages := {} };
    pure messages
  let restoreMessages (prevMessages : MessageLog) : CommandElabM Unit := do
    modify fun s => { s with messages := prevMessages ++ s.messages.errorsToWarnings }
  let prevMessages ← resetMessages
  let succeeded ← try
    x
    hasNoErrorMessages
  catch
    | ex@(Exception.error _ _) => do logException ex; pure false
    | Exception.internal id _  => do logError (← id.getName); pure false
  finally
    restoreMessages prevMessages
  if succeeded then
    throwError "unexpected success"

@[builtin_command_elab «check_failure»] def elabCheckFailure : CommandElab
  | `(#check_failure $term) => do
    failIfSucceeds <| elabCheckCore (ignoreStuckTC := false) (← `(#check $term))
  | _ => throwUnsupportedSyntax

/--
Elaborates the term, ensuring the result has no expression metavariables.
If there would be unsolved-for metavariables, tries hinting that the resulting type
is a monadic value with the `CommandElabM` monad or the `IO` monad.
-/
private def elabTermForEval (term : Syntax) : TermElabM Expr := do
  let ty ← mkFreshTypeMVar
  let e ← Term.elabTerm term ty
  synthesizeWithHinting ty
  let e ← instantiateMVars e
  if (← Term.logUnassignedUsingErrorInfos (← getMVars e)) then throwAbortTerm
  if ← isProof e then
    throwError m!"cannot evaluate, proofs are not computationally relevant"
  let e ← if (← isProp e) then mkDecide e else pure e
  if ← isType e then
    throwError m!"cannot evaluate, types are not computationally relevant"
  return e
where
  /-- Try different strategies to make `Term.synthesizeSyntheticMVarsNoPostponing` succeed. -/
  synthesizeWithHinting (ty : Expr) : TermElabM Unit := do
    Term.synthesizeSyntheticMVarsUsingDefault
    let s ← saveState
    try
      Term.synthesizeSyntheticMVarsNoPostponing
    catch ex =>
      let exS ← saveState
      s.restore true
      -- See if we can make `ty` be a monad application of `CommandElabM` or `IO`.
      try
        if ← isDefEq ty (← mkFreshMonadApp ``CommandElabM) then
          Term.synthesizeSyntheticMVarsNoPostponing
          return
      catch _ =>
        s.restore true
        try
          if ← isDefEq ty (← mkFreshMonadApp ``IO) then
            Term.synthesizeSyntheticMVarsNoPostponing
            return
        catch _ =>
          -- Neither strategy worked, so throw the original error.
          exS.restore true
          throw ex
  mkFreshMonadApp (n : Name) : MetaM Expr := do
    let m ← mkConstWithFreshMVarLevels n
    let (args, _, _) ← forallMetaBoundedTelescope (← inferType m) 1
    return mkAppN m args

private def addAndCompileExprForEval (declName : Name) (value : Expr) (allowSorry := false) : TermElabM Unit := do
  if value.hasSyntheticSorry then
    -- There is an elaboration error, don't evaluate!
    throwAbortTerm
  let value ← Term.levelMVarToParam (← instantiateMVars value)
  let type ← inferType value
  let us := collectLevelParams {} value |>.params
  let value ← instantiateMVars value
  let decl := Declaration.defnDecl {
    name        := declName
    levelParams := us.toList
    type        := type
    value       := value
    hints       := ReducibilityHints.opaque
    safety      := DefinitionSafety.unsafe
  }
  Term.ensureNoUnassignedMVars decl
  addAndCompile decl
  unless allowSorry do
    let axioms ← collectAxioms declName
    if axioms.contains ``sorryAx then
      throwError "\
        aborting evaluation since the expression depends on the 'sorry' axiom, \
        which can lead to runtime instability and crashes.\n\n\
        To evaluate anyway despite the risks, use the '#eval!' command."

register_builtin_option eval.pp : Bool := {
  defValue := true
  descr    := "('#eval' command) enables using 'ToExpr' instances to pretty print the result"
}

register_builtin_option eval.type : Bool := {
  defValue := true
  descr    := "('#eval' command) enables pretty printing the type of the result"
}

/-- Returns a representation of `e` using `MessageData`, or fails. -/
private def mkMessageData (e : Expr) (extraMsg : MetaM MessageData := pure "") : MetaM Expr := do
  (do guard <| eval.pp.get (← getOptions); mkAppM ``MessageData.ofExpr #[← mkAppM ``toExpr #[e]])
  <|> (do mkAppM ``MessageData.ofFormat #[← mkAppM ``repr #[e]])
  <|> (do mkAppM ``MessageData.ofFormat #[← mkAppM ``Std.Format.text #[← mkAppM ``toString #[e]]])
  <|> do throwError m!"could not synthesize a 'ToExpr', 'Repr', or 'ToString' instance for type{indentExpr (← inferType e)}{← extraMsg}"

/-- Returns a representation of `e` using `Format`, or fails. This is a fallback to `mkMessageData` in case `MessageData` isn't imported. -/
private def mkFormat (e : Expr) (extraMsg : MetaM MessageData := pure "") : MetaM Expr := do
  (mkAppM ``repr #[e]) <|> (do mkAppM ``Std.Format.text #[← mkAppM ``toString #[e]])
  <|> do throwError m!"could not synthesize a 'Repr' or 'ToString' instance for type{indentExpr (← inferType e)}{← extraMsg}"

unsafe def elabEvalCoreUnsafe (bang : Bool) (tk term : Syntax) : CommandElabM Unit := withRef tk do
  let declName := `_eval
  let log (ty : Expr) (f : MessageData) : CommandElabM Unit := do
    if eval.type.get (← getOptions) then
      logInfo m!"{f} : {ty}"
    else
      logInfo f
  -- Create an action given the name of the monad `mc`, the monad `m` itself,
  -- and an expression `e` to try to evaluate in this monad.
  let mkAct? (mc : Name) (m : Type → Type) [Monad m] [MonadEvalT m CommandElabM] (e : Expr) : TermElabM (Option (CommandElabM Unit)) := do
    let some e ← observing? (mkAppOptM ``MonadEvalT.monadEval #[none, mkConst mc, none, none, e])
      | return none
    let eType := e.appFn!.appArg!
    if ← isDefEq eType (mkConst ``Unit) then
      addAndCompileExprForEval declName e (allowSorry := bang)
      let mf ← evalConst (m Unit) declName
      return some do MonadEvalT.monadEval mf
    else
      let mf : m MessageData ←
        if (← getEnv).contains ``Lean.MessageData then
          let rf ← withLocalDeclD `x eType fun x => do mkLambdaFVars #[x] (← mkMessageData x)
          let mut r ← mkAppM ``Functor.map #[rf, e]
          addAndCompileExprForEval declName r (allowSorry := bang)
          evalConst (m MessageData) declName
        else
          let rf ← withLocalDeclD `x eType fun x => do mkLambdaFVars #[x] (← mkFormat x)
          let mut r ← mkAppM ``Functor.map #[rf, e]
          addAndCompileExprForEval declName r (allowSorry := bang)
          evalConst (m Format) declName
      return some do MonadEvalT.monadEval mf >>= log eType
  -- Generate an action without executing it. We use `withoutModifyingEnv` to ensure
  -- we don't pollute the environment with auxiliary declarations.
  let act : CommandElabM Unit ← liftTermElabM do Term.withDeclName declName do withoutModifyingEnv do
    let e ← elabTermForEval term
    if let some act ← mkAct? ``CommandElabM CommandElabM e
                    -- Fallbacks in case we are in the Lean package
                    <||> mkAct? ``TermElabM TermElabM e <||> mkAct? ``MetaM MetaM e <||> mkAct? ``CoreM CoreM e
                    -- Fallback in case nothing is imported
                    <||> mkAct? ``IO IO e then
      return act
    else
      -- No need to adapt pure values to `CommandElabM`
      let mkMonadDiagnosticMsg := do
        -- Augment the error message if this is a monad containing a value that is representable.
        try
          let some (m, ty) ← isTypeApp? (← inferType e) | failure
          guard <| (← isMonad? m).isSome
          -- Verify that there is a way to form some MessageData:
          (discard <| withLocalDeclD `x ty fun x => mkMessageData x)
            <|> (discard <| withLocalDeclD `x ty fun x => mkFormat x)
          pure m!"\n\nThis is due to a missing '{MessageData.ofConstName ``MonadEval}' instance \
            to adapt this monad to '{MessageData.ofConstName ``IO}' or '{MessageData.ofConstName ``CommandElabM}'."
        catch _ =>
          pure m!""
      let d : MessageData ←
        if (← getEnv).contains ``Lean.MessageData then
          let r ← mkMessageData e mkMonadDiagnosticMsg
          addAndCompileExprForEval declName r (allowSorry := bang)
          evalConst MessageData declName
        else
          let r ← mkFormat e mkMonadDiagnosticMsg
          addAndCompileExprForEval declName r (allowSorry := bang)
          evalConst Format declName
      let eType ← inferType e
      return do log eType d
  act

@[implemented_by elabEvalCoreUnsafe]
opaque elabEvalCore (bang : Bool) (tk term : Syntax) : CommandElabM Unit

@[builtin_command_elab «eval»]
def elabEval : CommandElab
  | `(#eval%$tk $term) => elabEvalCore false tk term
  | _ => throwUnsupportedSyntax

@[builtin_command_elab evalBang]
def elabEvalBang : CommandElab
  | `(Parser.Command.evalBang|#eval!%$tk $term) => elabEvalCore true tk term
  | _ => throwUnsupportedSyntax

private def checkImportsForRunCmds : CommandElabM Unit := do
  unless (← getEnv).contains ``CommandElabM do
    throwError "to use this command, include `import Lean.Elab.Command`"

@[builtin_command_elab runCmd]
def elabRunCmd : CommandElab
  | `(run_cmd $elems:doSeq) => do
    checkImportsForRunCmds
    (← liftTermElabM <| Term.withDeclName `_run_cmd <|
      unsafe Term.evalTerm (CommandElabM Unit)
        (mkApp (mkConst ``CommandElabM) (mkConst ``Unit))
        (← `(discard do $elems)))
  | _ => throwUnsupportedSyntax

@[builtin_command_elab runElab]
def elabRunElab : CommandElab
  | `(run_elab $elems:doSeq) => do
    checkImportsForRunCmds
    (← liftTermElabM <| Term.withDeclName `_run_elab <|
      unsafe Term.evalTerm (CommandElabM Unit)
        (mkApp (mkConst ``CommandElabM) (mkConst ``Unit))
        (← `(Command.liftTermElabM <| discard do $elems)))
  | _ => throwUnsupportedSyntax

@[builtin_command_elab runMeta]
def elabRunMeta : CommandElab := fun stx =>
  match stx with
  | `(run_meta $elems:doSeq) => do
     checkImportsForRunCmds
     let stxNew ← `(command| run_elab (show Lean.Meta.MetaM Unit from do $elems))
     withMacroExpansion stx stxNew do elabCommand stxNew
  | _ => throwUnsupportedSyntax

@[builtin_command_elab «synth»] def elabSynth : CommandElab := fun stx => do
  let term := stx[1]
  withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_synth_cmd do
    let inst ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let inst ← instantiateMVars inst
    let val  ← synthInstance inst
    logInfo val
    pure ()

@[builtin_command_elab «set_option»] def elabSetOption : CommandElab := fun stx => do
  let options ← Elab.elabSetOption stx[1] stx[3]
  modify fun s => { s with maxRecDepth := maxRecDepth.get options }
  modifyScope fun scope => { scope with opts := options }

@[builtin_macro Lean.Parser.Command.«in»] def expandInCmd : Macro
  | `($cmd₁ in%$tk $cmd₂) =>
    -- Limit ref variability for incrementality; see Note [Incremental Macros]
    withRef tk `(section $cmd₁:command $cmd₂ end)
  | _                 => Macro.throwUnsupported

@[builtin_command_elab Parser.Command.addDocString] def elabAddDeclDoc : CommandElab := fun stx => do
  match stx with
  | `($doc:docComment add_decl_doc $id) =>
    let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    unless ((← getEnv).getModuleIdxFor? declName).isNone do
      throwError "invalid 'add_decl_doc', declaration is in an imported module"
    if let .none ← findDeclarationRangesCore? declName then
      -- this is only relevant for declarations added without a declaration range
      -- in particular `Quot.mk` et al which are added by `init_quot`
      addAuxDeclarationRanges declName stx id
    addDocString declName (← getDocStringText doc)
  | _ => throwUnsupportedSyntax

@[builtin_command_elab Lean.Parser.Command.include] def elabInclude : CommandElab
  | `(Lean.Parser.Command.include| include $ids*) => do
    let sc ← getScope
    let vars ← sc.varDecls.concatMapM getBracketedBinderIds
    let mut uids := #[]
    for id in ids do
      if let some idx := vars.findIdx? (· == id.getId) then
        uids := uids.push sc.varUIds[idx]!
      else
        throwError "invalid 'include', variable '{id}' has not been declared in the current scope"
    modifyScope fun sc => { sc with
      includedVars := sc.includedVars ++ uids.toList
      omittedVars := sc.omittedVars.filter (!uids.contains ·) }
  | _ => throwUnsupportedSyntax

@[builtin_command_elab Lean.Parser.Command.omit] def elabOmit : CommandElab
  | `(Lean.Parser.Command.omit| omit $omits*) => do
    -- TODO: this really shouldn't have to re-elaborate section vars... they should come
    -- pre-elaborated
    let omittedVars ← runTermElabM fun vars => do
      Term.synthesizeSyntheticMVarsNoPostponing
      -- We don't want to store messages produced when elaborating `(getVarDecls s)` because they have already been saved when we elaborated the `variable`(s) command.
      -- So, we use `Core.resetMessageLog`.
      Core.resetMessageLog
      -- resolve each omit to variable user name or type pattern
      let elaboratedOmits : Array (Sum Name Expr) ← omits.mapM fun
        | `(ident| $id:ident) => pure <| Sum.inl id.getId
        | `(Lean.Parser.Term.instBinder| [$id : $_]) => pure <| Sum.inl id.getId
        | `(Lean.Parser.Term.instBinder| [$ty]) =>
          Sum.inr <$> Term.withoutErrToSorry (Term.elabTermAndSynthesize ty none)
        | _ => throwUnsupportedSyntax
      -- check that each omit is actually used in the end
      let mut omitsUsed := omits.map fun _ => false
      let mut omittedVars := #[]
      let mut revSectionFVars : Std.HashMap FVarId Name := {}
      for (uid, var) in (← read).sectionFVars do
        revSectionFVars := revSectionFVars.insert var.fvarId! uid
      for var in vars do
        let ldecl ← var.fvarId!.getDecl
        if let some idx := (← elaboratedOmits.findIdxM? fun
            | .inl id => return ldecl.userName == id
            | .inr ty => do
              let mctx ← getMCtx
              isDefEq ty ldecl.type <* setMCtx mctx) then
          if let some uid := revSectionFVars[var.fvarId!]? then
            omittedVars := omittedVars.push uid
            omitsUsed := omitsUsed.set! idx true
          else
            throwError "invalid 'omit', '{ldecl.userName}' has not been declared in the current scope"
      for o in omits, used in omitsUsed do
        unless used do
          throwError "'{o}' did not match any variables in the current scope"
      return omittedVars
    modifyScope fun sc => { sc with
      omittedVars := sc.omittedVars ++ omittedVars.toList
      includedVars := sc.includedVars.filter (!omittedVars.contains ·) }
  | _ => throwUnsupportedSyntax

@[builtin_command_elab Parser.Command.exit] def elabExit : CommandElab := fun _ =>
  logWarning "using 'exit' to interrupt Lean"

@[builtin_command_elab Parser.Command.import] def elabImport : CommandElab := fun _ =>
  throwError "invalid 'import' command, it must be used in the beginning of the file"

@[builtin_command_elab Parser.Command.eoi] def elabEoi : CommandElab := fun _ =>
  return

end Lean.Elab.Command
