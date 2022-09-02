/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.DeclarationRange
import Lean.DocString
import Lean.Util.CollectLevelParams
import Lean.Elab.Eval
import Lean.Elab.Command
import Lean.Elab.Open

namespace Lean.Elab.Command

@[builtinCommandElab moduleDoc] def elabModuleDoc : CommandElab := fun stx => do
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

private def checkAnonymousScope : List Scope → Bool
  | { header := "", .. } :: _   => true
  | _                           => false

private def checkEndHeader : Name → List Scope → Bool
  | .anonymous, _                             => true
  | .str p s,   { header := h, .. } :: scopes => h == s && checkEndHeader p scopes
  | _,          _                             => false

@[builtinCommandElab «namespace»] def elabNamespace : CommandElab := fun stx =>
  match stx with
  | `(namespace $n) => addNamespace n.getId
  | _               => throwUnsupportedSyntax

@[builtinCommandElab «section»] def elabSection : CommandElab := fun stx => do
  match stx with
  | `(section $header:ident) => addScopes (isNewNamespace := false) (isNoncomputable := false) header.getId
  | `(section)               => addScope (isNewNamespace := false) (isNoncomputable := false) "" (← getCurrNamespace)
  | _                        => throwUnsupportedSyntax

@[builtinCommandElab noncomputableSection] def elabNonComputableSection : CommandElab := fun stx => do
  match stx with
  | `(noncomputable section $header:ident) => addScopes (isNewNamespace := false) (isNoncomputable := true) header.getId
  | `(noncomputable section)               => addScope (isNewNamespace := false) (isNoncomputable := true) "" (← getCurrNamespace)
  | _                        => throwUnsupportedSyntax

@[builtinCommandElab «end»] def elabEnd : CommandElab := fun stx => do
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
    unless checkAnonymousScope scopes do
      throwError "invalid 'end', name is missing"
  | some header =>
    unless checkEndHeader header scopes do
      addCompletionInfo <| CompletionInfo.endSection stx (scopes.map fun scope => scope.header)
      throwError "invalid 'end', name mismatch"

private partial def elabChoiceAux (cmds : Array Syntax) (i : Nat) : CommandElabM Unit :=
  if h : i < cmds.size then
    let cmd := cmds.get ⟨i, h⟩;
    catchInternalId unsupportedSyntaxExceptionId
      (elabCommand cmd)
      (fun _ => elabChoiceAux cmds (i+1))
  else
    throwUnsupportedSyntax

@[builtinCommandElab choice] def elabChoice : CommandElab := fun stx =>
  elabChoiceAux stx.getArgs 0

@[builtinCommandElab «universe»] def elabUniverse : CommandElab := fun n => do
  n[1].forArgsM addUnivLevel

@[builtinCommandElab «init_quot»] def elabInitQuot : CommandElab := fun _ => do
  match (← getEnv).addDecl Declaration.quotDecl with
  | Except.ok env   => setEnv env
  | Except.error ex => throwError (ex.toMessageData (← getOptions))

@[builtinCommandElab «export»] def elabExport : CommandElab := fun stx => do
  let `(export $ns ($ids*)) := stx | throwUnsupportedSyntax
  let nss ← resolveNamespace ns
  let currNamespace ← getCurrNamespace
  if nss == [currNamespace] then throwError "invalid 'export', self export"
  let mut aliases := #[]
  for idStx in ids do
    let id := idStx.getId
    let declName ← resolveNameUsingNamespaces nss idStx
    aliases := aliases.push (currNamespace ++ id, declName)
  modify fun s => { s with env := aliases.foldl (init := s.env) fun env p => addAlias env p.1 p.2 }

@[builtinCommandElab «open»] def elabOpen : CommandElab
  | `(open $decl:openDecl) => do
    let openDecls ← elabOpenDecl decl
    modifyScope fun scope => { scope with openDecls := openDecls }
  | _ => throwUnsupportedSyntax

private def typelessBinder? : Syntax → Option (Array (TSyntax [`ident, `Lean.Parser.Term.hole]) × Bool)
  | `(bracketedBinder|($ids*)) => some <| (ids, true)
  | `(bracketedBinder|{$ids*}) => some <| (ids, false)
  | _                          => none

/--  If `id` is an identifier, return true if `ids` contains `id`. -/
private def containsId (ids : Array (TSyntax [`ident, ``Parser.Term.hole])) (id : TSyntax [`ident, ``Parser.Term.hole]) : Bool :=
  id.raw.isIdent && ids.any fun id' => id'.raw.getId == id.raw.getId

/--
  Auxiliary method for processing binder annotation update commands: `variable (α)` and `variable {α}`.
  The argument `binder` is the binder of the `variable` command.
  The method retuns an array containing the "residue", that is, variables that do not correspond to updates.
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
  for varDecl in varDecls do
    let (ids, ty?, explicit') ← match varDecl with
      | `(bracketedBinder|($ids* $[: $ty?]? $(annot?)?)) =>
        if annot?.isSome then
          for binderId in binderIds do
            if containsId ids binderId then
              throwErrorAt binderId "cannot update binder annotation of variables with default values/tactics"
        pure (ids, ty?, true)
      | `(bracketedBinder|{$ids* $[: $ty?]?}) =>
        pure (ids, ty?, false)
      | `(bracketedBinder|[$id : $_]) =>
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
          `(bracketedBinder| ($id $[: $ty?]?))
        else
          `(bracketedBinder| {$id $[: $ty?]?})
      for id in ids do
        if let some idx := binderIds.findIdx? fun binderId => binderId.raw.isIdent && binderId.raw.getId == id.raw.getId then
          binderIds := binderIds.eraseIdx idx
          modifiedVarDecls := true
          varDeclsNew := varDeclsNew.push (← mkBinder id explicit)
        else
          varDeclsNew := varDeclsNew.push (← mkBinder id explicit')
  if modifiedVarDecls then
    modifyScope fun scope => { scope with varDecls := varDeclsNew }
  if binderIds.size != binderIdsIniSize then
    binderIds.mapM fun binderId =>
      if explicit then
        `(bracketedBinder| ($binderId))
      else
        `(bracketedBinder| {$binderId})
  else
    return #[binder]

@[builtinCommandElab «variable»] def elabVariable : CommandElab
  | `(variable $binders*) => do
    -- Try to elaborate `binders` for sanity checking
    runTermElabM fun _ => Term.withAutoBoundImplicit <|
      Term.elabBinders binders fun _ => pure ()
    for binder in binders do
      let binders ← replaceBinderAnnotation binder
      -- Remark: if we want to produce error messages when variables shadow existing ones, here is the place to do it.
      for binder in binders do
        let varUIds ← getBracketedBinderIds binder |>.mapM (withFreshMacroScope ∘ MonadQuotation.addMacroScope)
        modifyScope fun scope => { scope with varDecls := scope.varDecls.push binder, varUIds := scope.varUIds ++ varUIds }
  | _ => throwUnsupportedSyntax

open Meta

def elabCheckCore (ignoreStuckTC : Bool) : CommandElab
  | `(#check%$tk $term) => withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_check do
    let e ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := ignoreStuckTC)
    let (e, _) ← Term.levelMVarToParam (← instantiateMVars e)
    let type ← inferType e
    unless e.isSyntheticSorry do
      logInfoAt tk m!"{e} : {type}"
  | _ => throwUnsupportedSyntax

@[builtinCommandElab Lean.Parser.Command.check] def elabCheck : CommandElab := elabCheckCore (ignoreStuckTC := true)

@[builtinCommandElab Lean.Parser.Command.reduce] def elabReduce : CommandElab
  | `(#reduce%$tk $term) => withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_reduce do
    let e ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let (e, _) ← Term.levelMVarToParam (← instantiateMVars e)
    -- TODO: add options or notation for setting the following parameters
    withTheReader Core.Context (fun ctx => { ctx with options := ctx.options.setBool `smartUnfolding false }) do
      let e ← withTransparency (mode := TransparencyMode.all) <| reduce e (skipProofs := false) (skipTypes := false)
      logInfoAt tk e
  | _ => throwUnsupportedSyntax

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

@[builtinCommandElab «check_failure»] def elabCheckFailure : CommandElab
  | `(#check_failure $term) => do
    failIfSucceeds <| elabCheckCore (ignoreStuckTC := false) (← `(#check $term))
  | _ => throwUnsupportedSyntax

private def mkEvalInstCore (evalClassName : Name) (e : Expr) : MetaM Expr := do
  let α    ← inferType e
  let u    ← getDecLevel α
  let inst := mkApp (Lean.mkConst evalClassName [u]) α
  try
    synthInstance inst
  catch _ =>
    -- Put `α` in WHNF and try again
    try
      let α ← whnf α
      synthInstance (mkApp (Lean.mkConst evalClassName [u]) α)
    catch _ =>
      -- Fully reduce `α` and try again
      try
        let α ← reduce (skipTypes := false) α
        synthInstance (mkApp (Lean.mkConst evalClassName [u]) α)
      catch _ =>
        throwError "expression{indentExpr e}\nhas type{indentExpr α}\nbut instance{indentExpr inst}\nfailed to be synthesized, this instance instructs Lean on how to display the resulting value, recall that any type implementing the `Repr` class also implements the `{evalClassName}` class"

private def mkRunMetaEval (e : Expr) : MetaM Expr :=
  withLocalDeclD `env (mkConst ``Lean.Environment) fun env =>
  withLocalDeclD `opts (mkConst ``Lean.Options) fun opts => do
    let α ← inferType e
    let u ← getDecLevel α
    let instVal ← mkEvalInstCore ``Lean.MetaEval e
    let e := mkAppN (mkConst ``Lean.runMetaEval [u]) #[α, instVal, env, opts, e]
    instantiateMVars (← mkLambdaFVars #[env, opts] e)

private def mkRunEval (e : Expr) : MetaM Expr := do
  let α ← inferType e
  let u ← getDecLevel α
  let instVal ← mkEvalInstCore ``Lean.Eval e
  instantiateMVars (mkAppN (mkConst ``Lean.runEval [u]) #[α, instVal, mkSimpleThunk e])

unsafe def elabEvalUnsafe : CommandElab
  | `(#eval%$tk $term) => do
    let declName := `_eval
    let addAndCompile (value : Expr) : TermElabM Unit := do
      let (value, _) ← Term.levelMVarToParam (← instantiateMVars value)
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
    -- Elaborate `term`
    let elabEvalTerm : TermElabM Expr := do
      let e ← Term.elabTerm term none
      Term.synthesizeSyntheticMVarsNoPostponing
      if (← Term.logUnassignedUsingErrorInfos (← getMVars e)) then throwAbortTerm
      if (← isProp e) then
        mkDecide e
      else
        return e
    -- Evaluate using term using `MetaEval` class.
    let elabMetaEval : CommandElabM Unit := do
      -- act? is `some act` if elaborated `term` has type `CommandElabM α`
      let act? ← runTermElabM fun _ => Term.withDeclName declName do
        let e ← elabEvalTerm
        let eType ← instantiateMVars (← inferType e)
        if eType.isAppOfArity ``CommandElabM 1 then
          let mut stx ← Term.exprToSyntax e
          unless (← isDefEq eType.appArg! (mkConst ``Unit)) do
            stx ← `($stx >>= fun v => IO.println (repr v))
          let act ← Lean.Elab.Term.evalTerm (CommandElabM Unit) (mkApp (mkConst ``CommandElabM) (mkConst ``Unit)) stx
          pure <| some act
        else
          let e ← mkRunMetaEval e
          let env ← getEnv
          let opts ← getOptions
          let act ← try addAndCompile e; evalConst (Environment → Options → IO (String × Except IO.Error Environment)) declName finally setEnv env
          let (out, res) ← act env opts -- we execute `act` using the environment
          logInfoAt tk out
          match res with
          | Except.error e => throwError e.toString
          | Except.ok env  => do setEnv env; pure none
      let some act := act? | return ()
      act
    -- Evaluate using term using `Eval` class.
    let elabEval : CommandElabM Unit := runTermElabM fun _ => Term.withDeclName declName do
      -- fall back to non-meta eval if MetaEval hasn't been defined yet
      -- modify e to `runEval e`
      let e ← mkRunEval (← elabEvalTerm)
      let env ← getEnv
      let act ← try addAndCompile e; evalConst (IO (String × Except IO.Error Unit)) declName finally setEnv env
      let (out, res) ← liftM (m := IO) act
      logInfoAt tk out
      match res with
      | Except.error e => throwError e.toString
      | Except.ok _    => pure ()
    if (← getEnv).contains ``Lean.MetaEval then do
      elabMetaEval
    else
      elabEval
  | _ => throwUnsupportedSyntax

@[builtinCommandElab «eval», implementedBy elabEvalUnsafe]
opaque elabEval : CommandElab

@[builtinCommandElab «synth»] def elabSynth : CommandElab := fun stx => do
  let term := stx[1]
  withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_synth_cmd do
    let inst ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let inst ← instantiateMVars inst
    let val  ← synthInstance inst
    logInfo val
    pure ()

@[builtinCommandElab «set_option»] def elabSetOption : CommandElab := fun stx => do
  let options ← Elab.elabSetOption stx[1] stx[2]
  modify fun s => { s with maxRecDepth := maxRecDepth.get options }
  modifyScope fun scope => { scope with opts := options }

@[builtinMacro Lean.Parser.Command.«in»] def expandInCmd : Macro
  | `($cmd₁ in $cmd₂) => `(section $cmd₁:command $cmd₂ end)
  | _                 => Macro.throwUnsupported

@[builtinCommandElab Parser.Command.addDocString] def elabAddDeclDoc : CommandElab := fun stx => do
  match stx with
  | `($doc:docComment add_decl_doc $id) =>
    let declName ← resolveGlobalConstNoOverloadWithInfo id
    addDocString declName (← getDocStringText doc)
  | _ => throwUnsupportedSyntax

end Lean.Elab.Command
