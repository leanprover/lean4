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

private def addScope (ref : Syntax) (isNewNamespace : Bool) (isNoncomputable : Bool) (header : String) (newNamespace : Name) : CommandElabM Unit := do
  modify fun s =>
    let newScope :=
      { s.scopes.head! with
        ref := ref
        header := header
        currNamespace := newNamespace
        isNoncomputable := s.scopes.head!.isNoncomputable || isNoncomputable }
    { s with
      env    := s.env.registerNamespace newNamespace,
      scopes := newScope :: s.scopes }
  pushScope
  if isNewNamespace then
    activateScoped newNamespace

private def addScopes (ref : Syntax) (isNewNamespace : Bool) (isNoncomputable : Bool) : Name → CommandElabM Unit
  | .anonymous => pure ()
  | .str p header => do
    addScopes ref isNewNamespace isNoncomputable p
    let currNamespace ← getCurrNamespace
    addScope ref isNewNamespace isNoncomputable header (if isNewNamespace then Name.mkStr currNamespace header else currNamespace)
  | _ => throwError "invalid scope"

private def addNamespace (ref : Syntax) (header : Name) : CommandElabM Unit :=
  addScopes ref (isNewNamespace := true) (isNoncomputable := false) header

private def popScopes (numScopes : Nat) : CommandElabM Unit :=
  for _ in [0:numScopes] do
    popScope

private def checkAnonymousScope : List Scope → Option Name
  | { header := "", .. } :: _ => none
  | { header := h, .. }  :: _ => some <| .mkSimple h
  | _                         => some .anonymous -- should not happen

@[builtin_command_elab «namespace»] def elabNamespace : CommandElab := fun stx =>
  match stx with
  | `(namespace $n) => addNamespace stx n.getId
  | _               => throwUnsupportedSyntax

@[builtin_command_elab «section»] def elabSection : CommandElab := fun stx => do
  match stx with
  | `(section $header:ident) => addScopes stx (isNewNamespace := false) (isNoncomputable := false) header.getId
  | `(section)               => addScope stx (isNewNamespace := false) (isNoncomputable := false) "" (← getCurrNamespace)
  | _                        => throwUnsupportedSyntax

@[builtin_command_elab noncomputableSection] def elabNonComputableSection : CommandElab := fun stx => do
  match stx with
  | `(noncomputable section $header:ident) => addScopes stx (isNewNamespace := false) (isNoncomputable := true) header.getId
  | `(noncomputable section)               => addScope stx (isNewNamespace := false) (isNoncomputable := true) "" (← getCurrNamespace)
  | _                        => throwUnsupportedSyntax

/-- Whether or not the scope was created using a `namespace` command. -/
def Scope.isNamespace (s : Scope) : Bool :=
  s.ref.isOfKind ``Parser.Command.«namespace»

/-- Whether or not the scope was created using a `section` command. -/
def Scope.isSection (s : Scope) : Bool :=
  s.ref.isOfKind ``Parser.Command.«section» || s.ref.isOfKind ``Parser.Command.noncomputableSection

@[builtin_command_elab «end»] def elabEnd : CommandElab := fun stx => do
  let header? := (stx.getArg 1).getOptionalIdent?
  let endSize :=
    match header? with
    | none   => 1
    | some n => n.getNumParts
  let scopes ← getScopes
  let maxDroppable := scopes.findIdx (fun scope => !(scope.isNamespace || scope.isSection))
  unless endSize ≤ maxDroppable do
    -- we drop all namespace/section scopes (leaving for example the "root" scope) before throwing an error
    let scopes' := scopes.drop maxDroppable
    modify fun s => { s with scopes := scopes' }
    popScopes maxDroppable
    throwError "invalid 'end', insufficient scopes"
  modify fun s => { s with scopes := s.scopes.drop endSize }
  popScopes endSize
  -- Now validate section/namespace headers.
  match header? with
  | none        =>
    if let some name := checkAnonymousScope scopes then
      throwError "invalid 'end', name is missing (expected {name})"
  | some header =>
    let comps := header.componentsRev
    let mut seenNamespace := false
    let mut seenSection := false
    for i in [0:comps.length] do
      let .str _ n := comps[i]! | throwError "invalid 'end', name has numeric component"
      let scope := scopes[i]!
      if scope.isNamespace then
        seenNamespace := true
        if seenSection then
          let n' := (comps.take i).foldr (init := Name.anonymous) (fun n acc => Name.appendCore acc n)
          throwError "invalid 'end', mixed ending of section {n'} and namespace {n}"
      else
        seenSection := true
        if seenNamespace then
          let n' := (comps.take i).foldr (init := Name.anonymous) (fun n acc => Name.appendCore acc n)
          throwError "invalid 'end', mixed ending of namespace {n'} and section {n}"
      if n != scope.header then
        addCompletionInfo <| CompletionInfo.endSection stx (scopes.map fun scope => scope.header)
        let name := (scopes.take (i + 1)).foldr (init := Name.anonymous) (fun n acc => .str acc n.header)
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
  if (← getScope).scopeRestriction == .global then
    logWarning m!"unexpected 'universe' in this context, only has local effect"
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
    if (← getScope).scopeRestriction == .global then
      logWarning m!"unexpected 'open' in this context, only has local effect"
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
  for varDecl in varDecls do
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
        `(bracketedBinderF| ($binderId))
      else
        `(bracketedBinderF| {$binderId})
  else
    return #[binder]

@[builtin_command_elab «variable»] def elabVariable : CommandElab
  | `(variable $binders*) => do
    if (← getScope).scopeRestriction == .global then
      logWarning m!"unexpected 'variable' in this context, only has local effect"
    -- Try to elaborate `binders` for sanity checking
    runTermElabM fun _ => Term.withSynthesize <| Term.withAutoBoundImplicit <|
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
    let e ← Term.levelMVarToParam (← instantiateMVars e)
    let type ← inferType e
    if e.isSyntheticSorry then
      return
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

unsafe def elabEvalCoreUnsafe (bang : Bool) (tk term : Syntax): CommandElabM Unit := do
    let declName := `_eval
    let addAndCompile (value : Expr) : TermElabM Unit := do
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
    -- Check for sorry axioms
    let checkSorry (declName : Name) : MetaM Unit := do
      unless bang do
        let axioms ← collectAxioms declName
        if axioms.contains ``sorryAx then
          throwError ("cannot evaluate expression that depends on the `sorry` axiom.\nUse `#eval!` to " ++
            "evaluate nevertheless (which may cause lean to crash).")
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
      -- Generate an action without executing it. We use `withoutModifyingEnv` to ensure
      -- we don't polute the environment with auxliary declarations.
      -- We have special support for `CommandElabM` to ensure `#eval` can be used to execute commands
      -- that modify `CommandElabM` state not just the `Environment`.
      let act : Sum (CommandElabM Unit) (Environment → Options → IO (String × Except IO.Error Environment)) ←
        runTermElabM fun _ => Term.withDeclName declName do withoutModifyingEnv do
          let e ← elabEvalTerm
          let eType ← instantiateMVars (← inferType e)
          if eType.isAppOfArity ``CommandElabM 1 then
            let mut stx ← Term.exprToSyntax e
            unless (← isDefEq eType.appArg! (mkConst ``Unit)) do
              stx ← `($stx >>= fun v => IO.println (repr v))
            let act ← Lean.Elab.Term.evalTerm (CommandElabM Unit) (mkApp (mkConst ``CommandElabM) (mkConst ``Unit)) stx
            pure <| Sum.inl act
          else
            let e ← mkRunMetaEval e
            addAndCompile e
            checkSorry declName
            let act ← evalConst (Environment → Options → IO (String × Except IO.Error Environment)) declName
            pure <| Sum.inr act
      match act with
      | .inl act => act
      | .inr act =>
        let (out, res) ← act (← getEnv) (← getOptions)
        logInfoAt tk out
        match res with
        | Except.error e => throwError e.toString
        | Except.ok env  => setEnv env; pure ()
    -- Evaluate using term using `Eval` class.
    let elabEval : CommandElabM Unit := runTermElabM fun _ => Term.withDeclName declName do withoutModifyingEnv do
      -- fall back to non-meta eval if MetaEval hasn't been defined yet
      -- modify e to `runEval e`
      let e ← mkRunEval (← elabEvalTerm)
      addAndCompile e
      checkSorry declName
      let act ← evalConst (IO (String × Except IO.Error Unit)) declName
      let (out, res) ← liftM (m := IO) act
      logInfoAt tk out
      match res with
      | Except.error e => throwError e.toString
      | Except.ok _    => pure ()
    if (← getEnv).contains ``Lean.MetaEval then do
      elabMetaEval
    else
      elabEval

@[implemented_by elabEvalCoreUnsafe]
opaque elabEvalCore (bang : Bool) (tk term : Syntax): CommandElabM Unit

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

@[builtin_command_elab Parser.Command.pushScope] def elabPushScope : CommandElab := fun stx => do
  let ref := stx.getArg 1
  let newScope := { (← getScope) with ref, header := "" }
  modify fun s => { s with scopes := newScope :: s.scopes }
  pushScope

@[builtin_command_elab Parser.Command.popScope] def elabPopScope : CommandElab := fun stx => do
  let ref := stx.getArg 1
  if let some idx := (← getScopes).findIdx? (fun scope => scope.ref == ref) then
    modify fun s => { s with scopes := s.scopes.drop (idx + 1) }
    popScopes (idx + 1)
    if idx > 0 then
      throwError "unexpected new scopes"
  else
    throwError "unmatched 'pop_scope%' (internal error: please report an issue)"

@[builtin_command_elab Parser.Command.withoutScopeRestriction] def elabWithoutScopeRestriction : CommandElab :=
  fun _ => setScopeRestriction .none

@[builtin_command_elab Parser.Command.withGlobalScopeRestriction] def elabWithGlobalScopeRestriction : CommandElab :=
  fun _ => setScopeRestriction .global

@[builtin_command_elab Parser.Command.withLocalScopeRestriction] def elabWithLocalScopeRestriction : CommandElab :=
  fun _ => setScopeRestriction .local

@[builtin_macro Lean.Parser.Command.«in»] def expandInCmd : Macro
  | `($cmd₁ in%$tk $cmd₂) =>
    -- Limit ref variability for incrementality; see Note [Incremental Macros]
    withRef tk
      `(push_scope% $(⟨tk⟩)
        with_local_scope_restriction%
        $cmd₁
        with_global_scope_restriction%
        $cmd₂
        pop_scope% $(⟨tk⟩))
  | _ => Macro.throwUnsupported

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
    let vars := (← getScope).varDecls.concatMap getBracketedBinderIds
    for id in ids do
      unless vars.contains id.getId do
        throwError "invalid 'include', variable '{id}' has not been declared in the current scope"
    modifyScope fun sc =>
      { sc with includedVars := sc.includedVars ++ ids.toList.map (·.getId) }
  | _ => throwUnsupportedSyntax

@[builtin_command_elab Parser.Command.exit] def elabExit : CommandElab := fun _ =>
  logWarning "using 'exit' to interrupt Lean"

@[builtin_command_elab Parser.Command.import] def elabImport : CommandElab := fun _ =>
  throwError "invalid 'import' command, it must be used in the beginning of the file"

@[builtin_command_elab Parser.Command.eoi] def elabEoi : CommandElab := fun _ =>
  return

end Lean.Elab.Command
