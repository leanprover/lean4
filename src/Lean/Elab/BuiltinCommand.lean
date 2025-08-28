/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Util.CollectLevelParams
public import Lean.Util.CollectAxioms
public import Lean.Meta.Reduce
public import Lean.Elab.DeclarationRange
public import Lean.Elab.Eval
public import Lean.Elab.Command
public import Lean.Elab.Open
public import Lean.Elab.SetOption
public import Init.System.Platform
public import Lean.Meta.Hint
public import Lean.Parser.Command

public section

namespace Lean.Elab.Command

@[builtin_command_elab moduleDoc] def elabModuleDoc : CommandElab := fun stx => do
  match stx[1] with
  | Syntax.atom _ val =>
    let doc := val.extract 0 (val.endPos - ⟨2⟩)
    let some range ← Elab.getDeclarationRange? stx
      | return  -- must be from partial syntax, ignore
    modifyEnv fun env => addMainModuleDoc env ⟨doc, range⟩
  | _ => throwErrorAt stx "unexpected module doc string{indentD stx[1]}"

private def addScope (isNewNamespace : Bool) (header : String) (newNamespace : Name)
    (isNoncomputable isPublic : Bool := false) (attrs : List (TSyntax ``Parser.Term.attrInstance) := []) :
    CommandElabM Unit := do
  modify fun s => { s with
    env    := s.env.registerNamespace newNamespace,
    scopes := { s.scopes.head! with
      header := header, currNamespace := newNamespace
      isNoncomputable := s.scopes.head!.isNoncomputable || isNoncomputable
      isPublic := s.scopes.head!.isPublic || isPublic
      attrs := s.scopes.head!.attrs ++ attrs
    } :: s.scopes
  }
  pushScope
  if isNewNamespace then
    activateScoped newNamespace

private def addScopes (header : Name) (isNewNamespace : Bool) (isNoncomputable isPublic : Bool := false)
    (attrs : List (TSyntax ``Parser.Term.attrInstance) := []) : CommandElabM Unit :=
  go header
where go
  | .anonymous => pure ()
  | .str p header => do
    go p
    let currNamespace ← getCurrNamespace
    addScope isNewNamespace header (if isNewNamespace then Name.mkStr currNamespace header else currNamespace) isNoncomputable isPublic attrs
  | _ => throwError "invalid scope"

private def addNamespace (header : Name) : CommandElabM Unit :=
  addScopes (isNewNamespace := true) (isNoncomputable := false) (attrs := []) header

def withNamespace {α} (ns : Name) (elabFn : CommandElabM α) : CommandElabM α := do
  addNamespace ns
  let a ← elabFn
  modify fun s => { s with scopes := s.scopes.drop ns.getNumParts }
  pure a

private def popScopes (numScopes : Nat) : CommandElabM Unit :=
  for _ in *...numScopes do
    popScope

private def innermostScopeName? : List Scope → Option Name
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
  | `(Parser.Command.section| $[@[expose%$expTk]]? $[public%$publicTk]? $[noncomputable%$ncTk]? section $(header?)?) =>
    -- TODO: allow more attributes?
    let attrs ← if expTk.isSome then
      pure [← `(Parser.Term.attrInstance| expose)]
    else
      pure []
    if let some header := header? then
      addScopes (isNewNamespace := false) (isNoncomputable := ncTk.isSome) (isPublic := publicTk.isSome) (attrs := attrs) header.getId
    else
      addScope (isNewNamespace := false) (isNoncomputable := ncTk.isSome) (isPublic := publicTk.isSome) (attrs := attrs) "" (← getCurrNamespace)
  | _                        => throwUnsupportedSyntax

@[builtin_command_elab InternalSyntax.end_local_scope] def elabEndLocalScope : CommandElab := fun _ => do
  setDelimitsLocal

/--
Produces a `Name` composed of the names of at most the innermost `n` scopes in `ss`, truncating if an
empty scope is reached (so that we do not suggest names like `Foo.«».Bar`).

If `n` is not specified, will use all scopes in `ss`.
-/
private def nameOfScopes : (ss : List Scope) → (n : Nat := ss.length) → Name
  | _, 0 => .anonymous
  | [], _ => .anonymous
  | s :: ss, n + 1 =>
    if s.header == "" then
      .anonymous
    else
    .str (nameOfScopes ss n) s.header

/--
Returns the first suffix of `base` that begins with `seg`, if one exists.

Note: this uses a naive, O(m*n) implementation for simplicity; we assume repeated partial overlap of
name components to be relatively uncommon, so that practical performance is closer to linear.
-/
private def findSuffixWithPrefix (base : Name) (seg : Name) : Option Name :=
  findSuffixMatch base seg true
where
  /--
  Helper for `findSuffixWithPrefix`. If `allowOffset` is `false`, then `seg` must be a suffix of
  `base`, not just a prefix of a suffix.
  -/
  findSuffixMatch : (base : Name) → (seg : Name) → (allowOffset : Bool) → Option Name
  | _, .anonymous, _ => some .anonymous
  | .anonymous, _, _ => none
  | .num p n, seg@(.num p' n'), allowOffset => do
    if n == n' then
      if let some nm := findSuffixMatch p p' (allowOffset := false) then
        return .num nm n
    if allowOffset then
      return .num (← findSuffixMatch p seg allowOffset) n
    else
      none
  | .str p s, seg@(.str p' s'), allowOffset => do
    if s == s' then
      if let some nm := findSuffixMatch p p' (allowOffset := false) then
        return .str nm s
    if allowOffset then
      return .str (← findSuffixMatch p seg allowOffset) s
    else
      none
  | .str p s, seg, allowOffset =>
    if allowOffset then
      return .str (← findSuffixMatch p seg allowOffset) s
    else
      none
  | .num p n, seg, allowOffset =>
    if allowOffset then
      return .num (← findSuffixMatch p seg allowOffset) n
    else
      none

private def throwNoScope : CommandElabM Unit :=
  throwError m!"Invalid `end`: There is no current scope to end"
    ++ .note m!"Scopes are introduced using `namespace` and `section`"

private def throwMissingName (name : Name) : CommandElabM Unit := do
  let hint ← liftCoreM <| MessageData.hint m!"To end the current scope `{name}`, specify its name:"
    #[← `(end $(mkIdent name))] (codeActionPrefix? := "Add scope name: ")
  throwError "Missing name after `end`: Expected the current scope name `{name}`{hint}"

/--
Produces a hint message with a suggestion to replace the name following `end` at the current ref
with the name given by `scopes` if there is only one active scope; otherwise, returns `none`.

Rationale: When there is only one active scope, only one valid `end` command is possible, so we
suggest it; if there are multiple, then it is harder to determine with confidence which the user
intended to end.
-/
private def mkSingleScopeReplacementHint? (scopes : List Scope) := do
  -- Recall that there is always an anonymous topmost scope, so `scopes.length = 2` when there is
  -- only one active scope:
  if scopes.length == 2 then
    let name := nameOfScopes scopes
    some <$> MessageData.hint m!"Use current scope name `{name}`:" #[(← `(end $(mkIdent name)))]
      (codeActionPrefix? := "Replace scope name: ")
  else
    return none

private def throwTooManyScopeComponents (header : Name) (scopes : List Scope) : CommandElabM Unit := do
  let hint ← liftCoreM do
    if let some hint ← mkSingleScopeReplacementHint? scopes then
      pure hint
    else
      let scopesName := nameOfScopes scopes
      pure <| MessageData.hint' m!"The name after `end` must be `{scopesName}` or some suffix thereof"
  throwError m!"Invalid name after `end`: `{header}` contains too many components" ++ hint

private def throwScopeNameMismatch (header : Name) (scopes : List Scope) (endSize : Nat)
    : CommandElabM Unit := do
  let correspondingScopes := nameOfScopes scopes endSize
  let allScopes := nameOfScopes scopes
  let help ← liftCoreM do
    if let some hint ← mkSingleScopeReplacementHint? scopes then
      pure hint
    else if let some suffix := findSuffixWithPrefix allScopes header then
      let hintMsg := m!"If you meant to end the outer scope(s) `{header}`, you must end all the \
        intervening scopes `{suffix}`:"
      MessageData.hint hintMsg #[← `(end $(mkIdent suffix))]
        (codeActionPrefix? := "Add intervening scopes: ")
    else if correspondingScopes != allScopes then
      pure <| .note m!"The current scopes are `{allScopes}`"
    else pure .nil
  throwError m!"Invalid name after `end`: Expected `{correspondingScopes}`, but found `{header}`" ++ help

private def throwUnnecessaryScopeName (header : Name) : CommandElabM Unit := do
  let hintMsg := m!"Delete the name `{header}` to end the current unnamed scope; outer named scopes \
    can then be closed using additional `end` command(s):"
  let hint ← liftCoreM <| MessageData.hint hintMsg #[← `(end)] (codeActionPrefix? := "Delete name: ")
  throwError m!"Unexpected name `{header}` after `end`: The current section is unnamed" ++ hint

@[builtin_command_elab «end»] def elabEnd : CommandElab := fun stx => do
  let header? := (stx.getArg 1).getOptionalIdent?
  let endSize : Nat := match header? with
    | none   => 1
    | some n => n.getNumParts
  let scopes ← getScopes
  let numScopes := scopes.length
  if numScopes == 1 then
    throwNoScope
  match header? with
  | none        =>
    if let some name := innermostScopeName? scopes then
      throwMissingName name
  | some header =>
    if endSize >= numScopes then
      throwTooManyScopeComponents header scopes
    else
      let scopesName := nameOfScopes scopes endSize
      if scopesName != header then
        if scopesName == .anonymous then
          throwUnnecessaryScopeName header
        else
          throwScopeNameMismatch header scopes endSize
  modify fun s => {s with scopes := s.scopes.drop endSize }
  popScopes endSize

private partial def elabChoiceAux (cmds : Array Syntax) (i : Nat) : CommandElabM Unit :=
  if h : i < cmds.size then
    catchInternalId unsupportedSyntaxExceptionId
      (elabCommand cmds[i])
      (fun _ => elabChoiceAux cmds (i+1))
  else
    throwUnsupportedSyntax

@[builtin_command_elab choice] def elabChoice : CommandElab := fun stx =>
  elabChoiceAux stx.getArgs 0

@[builtin_command_elab «universe»] def elabUniverse : CommandElab := fun n => do
  n[1].forArgsM addUnivLevel

@[builtin_command_elab «init_quot»] def elabInitQuot : CommandElab := fun _ => do
  liftCoreM <| addDecl Declaration.quotDecl

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

private def typelessBinder? : Syntax → Option (Array (TSyntax [`ident, `Lean.Parser.Term.hole]) × BinderInfo)
  | `(bracketedBinderF|($ids*))     => some (ids, .default)
  | `(bracketedBinderF|{$ids*})     => some (ids, .implicit)
  | `(bracketedBinderF|⦃$ids*⦄)     => some (ids, .strictImplicit)
  | `(bracketedBinderF|[$id:ident]) => some (#[id], .instImplicit)
  | _                               => none

/--  If `id` is an identifier, return true if `ids` contains `id`. -/
private def containsId (ids : Array (TSyntax [`ident, ``Parser.Term.hole])) (id : TSyntax [`ident, ``Parser.Term.hole]) : Bool :=
  id.raw.isIdent && ids.any fun id' => id'.raw.getId == id.raw.getId

/--
  Auxiliary method for processing binder annotation update commands:
  `variable (α)`, `variable {α}`, `variable ⦃α⦄`, and `variable [α]`.
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
  let some (binderIds, binderInfo) := typelessBinder? binder | return #[binder]
  let varDecls := (← getScope).varDecls
  let mut varDeclsNew := #[]
  let mut binderIds := binderIds
  let mut binderIdsIniSize := binderIds.size
  let mut modifiedVarDecls := false
  -- Go through declarations in reverse to respect shadowing
  for varDecl in varDecls.reverse do
    let (ids, ty?, binderInfo') ← match varDecl with
      | `(bracketedBinderF|($ids* $[: $ty?]? $(annot?)?)) =>
        if annot?.isSome then
          for binderId in binderIds do
            if containsId ids binderId then
              throwErrorAt binderId "cannot update binder annotation of variables with default values/tactics"
        pure (ids, ty?, .default)
      | `(bracketedBinderF|{$ids* $[: $ty?]?}) =>
        pure (ids, ty?, .implicit)
      | `(bracketedBinderF|⦃$ids* $[: $ty?]?⦄) =>
        pure (ids, ty?, .strictImplicit)
      | `(bracketedBinderF|[$id : $ty]) =>
        pure (#[⟨id⟩], some ty, .instImplicit)
      | _ =>
        varDeclsNew := varDeclsNew.push varDecl; continue
    if binderInfo == binderInfo' then
      -- no update, ensure we don't have redundant annotations.
      for binderId in binderIds do
        if containsId ids binderId then
          throwErrorAt binderId "redundant binder annotation update"
      varDeclsNew := varDeclsNew.push varDecl
    else if binderIds.all fun binderId => !containsId ids binderId then
      -- `binderIds` and `ids` are disjoint
      varDeclsNew := varDeclsNew.push varDecl
    else
      let mkBinder (id : TSyntax [`ident, ``Parser.Term.hole]) (binderInfo : BinderInfo) : CommandElabM (TSyntax ``Parser.Term.bracketedBinder) :=
        match binderInfo with
        | .default => `(bracketedBinderF| ($id $[: $ty?]?))
        | .implicit => `(bracketedBinderF| {$id $[: $ty?]?})
        | .strictImplicit => `(bracketedBinderF| {{$id $[: $ty?]?}})
        | .instImplicit => do
          let some ty := ty?
            | throwErrorAt binder "cannot update binder annotation of variable `{id}` to instance implicit:\n\
                variable was originally declared without an explicit type"
          `(bracketedBinderF| [$(⟨id⟩) : $ty])
      for id in ids.reverse do
        if let some idx := binderIds.findFinIdx? fun binderId => binderId.raw.isIdent && binderId.raw.getId == id.raw.getId then
          binderIds := binderIds.eraseIdx idx
          modifiedVarDecls := true
          let newBinder ← mkBinder id binderInfo
          if binderInfo.isInstImplicit then
            -- We elaborate the new binder to make sure it's valid as instance implicit
            try
              runTermElabM fun _ => Term.withSynthesize <| Term.withAutoBoundImplicit <|
                Term.elabBinder newBinder fun _ => pure ()
            catch e =>
              throwErrorAt binder m!"cannot update binder annotation of variable `{id}` to instance implicit:\n\
                {e.toMessageData}"
          varDeclsNew := varDeclsNew.push (← mkBinder id binderInfo)
        else
          varDeclsNew := varDeclsNew.push (← mkBinder id binderInfo')
  if modifiedVarDecls then
    modifyScope fun scope => { scope with varDecls := varDeclsNew.reverse }
  if binderIds.size != binderIdsIniSize then
    binderIds.mapM fun binderId =>
      match binderInfo with
        | .default => `(bracketedBinderF| ($binderId))
        | .implicit => `(bracketedBinderF| {$binderId})
        | .strictImplicit => `(bracketedBinderF| {{$binderId}})
        | .instImplicit => throwUnsupportedSyntax
  else
    return #[binder]

@[builtin_command_elab «variable»] def elabVariable : CommandElab
  | `(variable%$tk $binders*) => do
    let binders ← binders.flatMapM replaceBinderAnnotation
    -- Try to elaborate `binders` for sanity checking
    runTermElabM fun _ => Term.withSynthesize <| Term.withAutoBoundImplicit <|
      Term.elabBinders binders fun xs => do
        -- Determine the set of auto-implicits for this variable command and add an inlay hint
        -- for them. We will only actually add the auto-implicits to a type when the variables
        -- declared here are used in some other declaration, but this is nonetheless the right
        -- place to display the inlay hint.
        let _ ← Term.addAutoBoundImplicits xs (tk.getTailPos? (canonicalOnly := true))
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
    modify fun s => { s with messages := prevMessages ++ s.messages.errorsToInfos }
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

open Lean.Parser.Command.InternalSyntax in
@[builtin_macro Lean.Parser.Command.«in»] def expandInCmd : Macro
  | `($cmd₁ in%$tk $cmd₂) =>
    -- Limit ref variability for incrementality; see Note [Incremental Macros]
    withRef tk `(section $cmd₁:command $endLocalScopeSyntax:command $cmd₂ end)
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
      addDeclarationRangesFromSyntax declName stx id
    addDocString declName doc
  | _ => throwUnsupportedSyntax

@[builtin_command_elab Lean.Parser.Command.include] def elabInclude : CommandElab
  | `(Lean.Parser.Command.include| include $ids*) => do
    let sc ← getScope
    let vars ← sc.varDecls.flatMapM getBracketedBinderIds
    let mut uids := #[]
    for id in ids do
      if let some idx := vars.findIdx? (· == id.getId) then
        uids := uids.push sc.varUIds[idx]!
      else
        throwError "invalid 'include', variable `{id}` has not been declared in the current scope"
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
            throwError "invalid 'omit', `{ldecl.userName}` has not been declared in the current scope"
      for o in omits, used in omitsUsed do
        unless used do
          throwError "`{o}` did not match any variables in the current scope"
      return omittedVars
    modifyScope fun sc => { sc with
      omittedVars := sc.omittedVars ++ omittedVars.toList
      includedVars := sc.includedVars.filter (!omittedVars.contains ·) }
  | _ => throwUnsupportedSyntax

@[builtin_command_elab version] def elabVersion : CommandElab := fun _ => do
  let mut target := System.Platform.target
  if target.isEmpty then target := "unknown"
  -- Only one should be set, but good to know if multiple are set in error.
  let platforms :=
    (if System.Platform.isWindows then [" Windows"] else [])
    ++ (if System.Platform.isOSX then [" macOS"] else [])
    ++ (if System.Platform.isEmscripten then [" Emscripten"] else [])
  logInfo m!"Lean {Lean.versionString}\nTarget: {target}{String.join platforms}"

@[builtin_command_elab Parser.Command.exit] def elabExit : CommandElab := fun _ =>
  logWarning "using 'exit' to interrupt Lean"

@[builtin_command_elab Parser.Command.import] def elabImport : CommandElab := fun _ =>
  throwError "invalid 'import' command, it must be used in the beginning of the file"

@[builtin_command_elab Parser.Command.eoi] def elabEoi : CommandElab := fun _ =>
  return

@[builtin_command_elab Parser.Command.where] def elabWhere : CommandElab := fun _ => do
  let scope ← getScope
  let mut msg : Array MessageData := #[]
  -- Noncomputable
  if scope.isNoncomputable then
    msg := msg.push <| ← `(Parser.Command.section| noncomputable section)
  -- Namespace
  if !scope.currNamespace.isAnonymous then
    msg := msg.push <| ← `(command| namespace $(mkIdent scope.currNamespace))
  -- Open namespaces
  if let some openMsg ← describeOpenDecls scope.openDecls.reverse then
    msg := msg.push openMsg
  -- Universe levels
  if !scope.levelNames.isEmpty then
    let levels := scope.levelNames.reverse.map mkIdent
    msg := msg.push <| ← `(command| universe $levels.toArray*)
  -- Variables
  if !scope.varDecls.isEmpty then
    let varDecls : Array (TSyntax `Lean.Parser.Term.bracketedBinder) := scope.varDecls.map (⟨·.raw.unsetTrailing⟩)
    msg := msg.push <| ← `(command| variable $varDecls*)
  -- Included variables
  if !scope.includedVars.isEmpty then
    msg := msg.push <| ← `(command| include $(scope.includedVars.toArray.map (mkIdent ·.eraseMacroScopes))*)
  -- Options
  if let some optionsMsg ← describeOptions scope.opts then
    msg := msg.push optionsMsg
  if msg.isEmpty then
    logInfo m!"-- In root namespace with initial scope"
  else
    logInfo <| MessageData.joinSep msg.toList "\n\n"
where
  /--
  'Delaborate' open declarations.
  Current limitations:
  - does not check whether or not successive namespaces need `_root_`
  - does not combine commands with `renaming` clauses into a single command
  -/
  describeOpenDecls (ds : List OpenDecl) : CommandElabM (Option MessageData) := do
    let mut lines : Array MessageData := #[]
    let mut simple : Array Name := #[]
    let flush (lines : Array MessageData) (simple : Array Name) : CommandElabM (Array MessageData × Array Name) := do
      if simple.isEmpty then
        return (lines, simple)
      else
        return (lines.push <| ← `(command| open $(simple.map mkIdent)*), #[])
    for d in ds do
      match d with
      | .explicit id decl =>
        (lines, simple) ← flush lines simple
        let ns := decl.getPrefix
        let «from» := Name.mkSimple decl.getString!
        lines := lines.push <| ← `(command| open $(mkIdent ns) renaming $(mkIdent «from») → $(mkIdent id))
      | .simple ns ex =>
        if ex == [] then
          simple := simple.push ns
        else
          (lines, simple) ← flush lines simple
          lines := lines.push <| ← `(command| open $(mkIdent ns) hiding $[$(ex.toArray.map mkIdent)]*)
    (lines, _) ← flush lines simple
    return if lines.isEmpty then none else MessageData.joinSep lines.toList "\n"

  describeOptions (opts : Options) : CommandElabM (Option MessageData) := do
    let mut lines : Array MessageData := #[]
    let decls ← getOptionDecls
    for (name, val) in opts do
      -- `#guard_msgs` sets this option internally, we don't want it to end up in its output
      if name == `Elab.async then
        continue
      let (isSet, isUnknown) :=
        match decls.find? name with
        | some decl => (decl.defValue != val, false)
        | none      => (true, true)
      if isSet then
        let cmd : TSyntax `command ←
          match val with
          | .ofBool true  => `(set_option $(mkIdent name) true)
          | .ofBool false => `(set_option $(mkIdent name) false)
          | .ofString str => `(set_option $(mkIdent name) $(Syntax.mkStrLit str))
          | .ofNat n      => `(set_option $(mkIdent name) $(Syntax.mkNatLit n))
          | _             => `(set_option $(mkIdent name) 0 /- unrepresentable value -/)
        if isUnknown then
          lines := lines.push m!"-- {cmd} -- unknown option"
        else
          lines := lines.push cmd
    return if lines.isEmpty then none else MessageData.joinSep lines.toList "\n"

@[builtin_command_elab Parser.Command.withExporting] def elabWithExporting : CommandElab
  | `(Parser.Command.withExporting| #with_exporting $cmd) =>
    withExporting do
      elabCommand cmd
  | _ => throwUnsupportedSyntax

@[builtin_command_elab Parser.Command.dumpAsyncEnvState] def elabDumpAsyncEnvState : CommandElab :=
  fun _ => do
    let env ← getEnv
    IO.eprintln (← env.dbgFormatAsyncState)

end Lean.Elab.Command
