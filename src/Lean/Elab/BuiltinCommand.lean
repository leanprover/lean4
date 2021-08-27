/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.DocString
import Lean.Elab.Command
import Lean.Elab.Open

namespace Lean.Elab.Command

@[builtinCommandElab moduleDoc] def elabModuleDoc : CommandElab := fun stx =>
   match stx[1] with
   | Syntax.atom _ val =>
     let doc := val.extract 0 (val.bsize - 2)
     modifyEnv fun env => addMainModuleDoc env doc
   | _ => throwErrorAt stx "unexpected module doc string{indentD stx[1]}"

private def addScope (isNewNamespace : Bool) (header : String) (newNamespace : Name) : CommandElabM Unit := do
  modify fun s => { s with
    env    := s.env.registerNamespace newNamespace,
    scopes := { s.scopes.head! with header := header, currNamespace := newNamespace } :: s.scopes
  }
  pushScope
  if isNewNamespace then
    activateScoped newNamespace

private def addScopes (isNewNamespace : Bool) : Name → CommandElabM Unit
  | Name.anonymous => pure ()
  | Name.str p header _ => do
    addScopes isNewNamespace p
    let currNamespace ← getCurrNamespace
    addScope isNewNamespace header (if isNewNamespace then Name.mkStr currNamespace header else currNamespace)
  | _ => throwError "invalid scope"

private def addNamespace (header : Name) : CommandElabM Unit :=
  addScopes (isNewNamespace := true) header

def withNamespace {α} (ns : Name) (elabFn : CommandElabM α) : CommandElabM α := do
  addNamespace ns
  let a ← elabFn
  modify fun s => { s with scopes := s.scopes.drop ns.getNumParts }
  pure a

private def popScopes (numScopes : Nat) : CommandElabM Unit :=
  for i in [0:numScopes] do
    popScope

private def checkAnonymousScope : List Scope → Bool
  | { header := "", .. } :: _   => true
  | _                           => false

private def checkEndHeader : Name → List Scope → Bool
  | Name.anonymous, _                             => true
  | Name.str p s _, { header := h, .. } :: scopes => h == s && checkEndHeader p scopes
  | _,              _                             => false

@[builtinCommandElab «namespace»] def elabNamespace : CommandElab := fun stx =>
  match stx with
  | `(namespace $n) => addNamespace n.getId
  | _               => throwUnsupportedSyntax

@[builtinCommandElab «section»] def elabSection : CommandElab := fun stx =>
  match stx with
  | `(section $header:ident) => addScopes (isNewNamespace := false) header.getId
  | `(section)               => do let currNamespace ← getCurrNamespace; addScope (isNewNamespace := false) "" currNamespace
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
      (fun ex => elabChoiceAux cmds (i+1))
  else
    throwUnsupportedSyntax

@[builtinCommandElab choice] def elbChoice : CommandElab := fun stx =>
  elabChoiceAux stx.getArgs 0

@[builtinCommandElab «universe»] def elabUniverse : CommandElab := fun n => do
  n[1].forArgsM addUnivLevel

@[builtinCommandElab «init_quot»] def elabInitQuot : CommandElab := fun stx => do
  match (← getEnv).addDecl Declaration.quotDecl with
  | Except.ok env   => setEnv env
  | Except.error ex => throwError (ex.toMessageData (← getOptions))

@[builtinCommandElab «export»] def elabExport : CommandElab := fun stx => do
  -- `stx` is of the form (Command.export "export" <namespace> "(" (null <ids>*) ")")
  let id  := stx[1].getId
  let ns ← resolveNamespace id
  let currNamespace ← getCurrNamespace
  if ns == currNamespace then throwError "invalid 'export', self export"
  let env ← getEnv
  let ids := stx[3].getArgs
  let aliases ← ids.foldlM (init := []) fun (aliases : List (Name × Name)) (idStx : Syntax) => do
    let id := idStx.getId
    let declName ← resolveOpenDeclId ns idStx
    pure <| (currNamespace ++ id, declName) :: aliases
  modify fun s => { s with env := aliases.foldl (init := s.env) fun env p => addAlias env p.1 p.2 }

@[builtinCommandElab «open»] def elabOpen : CommandElab := fun n => do
  let openDecls ← elabOpenDecl n[1]
  modifyScope fun scope => { scope with openDecls := openDecls }

private def typelessBinder? : Syntax → Option (Array Name × Bool)
  | `(bracketedBinder|($ids*)) => some <| (ids.map Syntax.getId, true)
  | `(bracketedBinder|{$ids*}) => some <| (ids.map Syntax.getId, false)
  | _                          => none

-- This function is used to implement the `variable` command that updates binder annotations.
private def matchBinderNames (ids : Array Syntax) (binderNames : Array Name) : CommandElabM Bool :=
  let ids := ids.map Syntax.getId
  /-
    TODO: allow users to update the annotation of some of the ids.
    The current application supports the common case
    ```
    variable (α : Type)
    ...
    variable {α : Type}
    ```
  -/
  if ids == binderNames then
    return true
  else if binderNames.any ids.contains then
    /- We currently do not split binder blocks. -/
    throwError "failed to update variable binder annotation" -- TODO: improve error message
  else
    return false

/--
  Auxiliary method for processing binder annotation update commands: `variable (α)` and `variable {α}`.
  The argument `binder` is the binder of the `variable` command.
  The method retuns `true` if the binder annotation was updated.
  Remark: we currently do not suppor updates of the form
  ```
  variable (α β : Type)
  ...
  variable {α} -- trying to update part of the binder block defined above.
  ```
-/
private def replaceBinderAnnotation (binder : Syntax) : CommandElabM Bool := do
  if let some (binderNames, explicit) := typelessBinder? binder then
    let varDecls := (← getScope).varDecls
    let mut varDeclsNew := #[]
    let mut found := false
    for varDecl in varDecls do
      if let some (ids, ty?, annot?) :=
        match varDecl with
        | `(bracketedBinder|($ids* $[: $ty?]? $(annot?)?)) => some (ids, ty?, annot?)
        | `(bracketedBinder|{$ids* $[: $ty?]?})            => some (ids, ty?, none)
        | `(bracketedBinder|[$id : $ty])                   => some (#[id], some ty, none)
        | _                                                => none
      then
        if (← matchBinderNames ids binderNames) then
          if annot?.isSome then
            throwError "cannot update binder annotation of variables with default values/tactics"
          if explicit then
            varDeclsNew := varDeclsNew.push (← `(bracketedBinder| ($ids* $[: $ty?]?)))
          else
            varDeclsNew := varDeclsNew.push (← `(bracketedBinder| {$ids* $[: $ty?]?}))
          found := true
        else
          varDeclsNew := varDeclsNew.push varDecl
      else
        varDeclsNew := varDeclsNew.push varDecl
    if found then
      modifyScope fun scope => { scope with varDecls := varDeclsNew }
      return true
    else
      return false
  else
    return false

@[builtinCommandElab «variable»] def elabVariable : CommandElab
  | `(variable $binders*) => do
    -- Try to elaborate `binders` for sanity checking
    runTermElabM none fun _ => Term.withAutoBoundImplicit <|
      Term.elabBinders binders fun _ => pure ()
    for binder in binders do
      unless (← replaceBinderAnnotation binder) do
        let varUIds ← getBracketedBinderIds binder |>.mapM (withFreshMacroScope ∘ MonadQuotation.addMacroScope)
        modifyScope fun scope => { scope with varDecls := scope.varDecls.push binder, varUIds := scope.varUIds ++ varUIds }
  | _ => throwUnsupportedSyntax

open Meta

@[builtinCommandElab Lean.Parser.Command.check] def elabCheck : CommandElab
  | `(#check%$tk $term) => withoutModifyingEnv $ runTermElabM (some `_check) fun _ => do
    let e ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let (e, _) ← Term.levelMVarToParam (← instantiateMVars e)
    let type ← inferType e
    unless e.isSyntheticSorry do
      logInfoAt tk m!"{e} : {type}"
  | _ => throwUnsupportedSyntax

@[builtinCommandElab Lean.Parser.Command.reduce] def elabReduce : CommandElab
  | `(#reduce%$tk $term) => withoutModifyingEnv <| runTermElabM (some `_check) fun _ => do
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
  let succeeded ←
    try
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
    failIfSucceeds <| elabCheck (← `(#check $term))
  | _ => throwUnsupportedSyntax

unsafe def elabEvalUnsafe : CommandElab
  | `(#eval%$tk $term) => do
    let n := `_eval
    let ctx ← read
    let addAndCompile (value : Expr) : TermElabM Unit := do
      let type ← inferType value
      let decl := Declaration.defnDecl {
        name        := n
        levelParams := []
        type        := type
        value       := value
        hints       := ReducibilityHints.opaque
        safety      := DefinitionSafety.unsafe
      }
      Term.ensureNoUnassignedMVars decl
      addAndCompile decl
    let elabEvalTerm : TermElabM Expr := do
      let e ← Term.elabTerm term none
      Term.synthesizeSyntheticMVarsNoPostponing
      if (← isProp e) then
        mkDecide e
      else
        return e
    let elabMetaEval : CommandElabM Unit := runTermElabM (some n) fun _ => do
      let e ← elabEvalTerm
      let e ← withLocalDeclD `env (mkConst ``Lean.Environment) fun env =>
          withLocalDeclD `opts (mkConst ``Lean.Options) fun opts => do
            let e ← mkAppM ``Lean.runMetaEval #[env, opts, e];
            mkLambdaFVars #[env, opts] e
      let env ← getEnv
      let opts ← getOptions
      let act ← try addAndCompile e; evalConst (Environment → Options → IO (String × Except IO.Error Environment)) n finally setEnv env
      let (out, res) ← act env opts -- we execute `act` using the environment
      logInfoAt tk out
      match res with
      | Except.error e => throwError e.toString
      | Except.ok env  => do setEnv env; pure ()
    let elabEval : CommandElabM Unit := runTermElabM (some n) fun _ => do
      -- fall back to non-meta eval if MetaEval hasn't been defined yet
      -- modify e to `runEval e`
      let e ← elabEvalTerm
      let e := mkSimpleThunk e
      let e ← mkAppM ``Lean.runEval #[e]
      let env ← getEnv
      let act ← try addAndCompile e; evalConst (IO (String × Except IO.Error Unit)) n finally setEnv env
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
constant elabEval : CommandElab

@[builtinCommandElab «synth»] def elabSynth : CommandElab := fun stx => do
  let term := stx[1]
  withoutModifyingEnv <| runTermElabM `_synth_cmd fun _ => do
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

@[builtinMacro Lean.Parser.Command.«in»] def expandInCmd : Macro := fun stx => do
  let cmd₁ := stx[0]
  let cmd₂ := stx[2]
  `(section $cmd₁:command $cmd₂:command end)

end Lean.Elab.Command
