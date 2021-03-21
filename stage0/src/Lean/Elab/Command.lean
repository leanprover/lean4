/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Parser.Command
import Lean.ResolveName
import Lean.Meta.Reduce
import Lean.Elab.Log
import Lean.Elab.Term
import Lean.Elab.Binders
import Lean.Elab.SyntheticMVars
import Lean.Elab.DeclModifiers
import Lean.Elab.InfoTree
import Lean.Elab.Open
import Lean.Elab.SetOption

namespace Lean.Elab.Command

structure Scope where
  header        : String
  opts          : Options := {}
  currNamespace : Name := Name.anonymous
  openDecls     : List OpenDecl := []
  levelNames    : List Name := []
  /-- section variables as `bracketedBinder`s -/
  varDecls      : Array Syntax := #[]
  /-- Globally unique internal identifiers for the `varDecls` -/
  varUIds       : Array Name := #[]
  deriving Inhabited

structure State where
  env            : Environment
  messages       : MessageLog := {}
  scopes         : List Scope := [{ header := "" }]
  nextMacroScope : Nat := firstFrontendMacroScope + 1
  maxRecDepth    : Nat
  nextInstIdx    : Nat := 1 -- for generating anonymous instance names
  ngen           : NameGenerator := {}
  infoState      : InfoState := {}
  deriving Inhabited

structure Context where
  fileName       : String
  fileMap        : FileMap
  currRecDepth   : Nat := 0
  cmdPos         : String.Pos := 0
  macroStack     : MacroStack := []
  currMacroScope : MacroScope := firstFrontendMacroScope
  ref            : Syntax := Syntax.missing

abbrev CommandElabCoreM (ε) := ReaderT Context $ StateRefT State $ EIO ε
abbrev CommandElabM := CommandElabCoreM Exception
abbrev CommandElab  := Syntax → CommandElabM Unit
abbrev Linter := Syntax → CommandElabM Unit

def mkState (env : Environment) (messages : MessageLog := {}) (opts : Options := {}) : State := {
  env         := env
  messages    := messages
  scopes      := [{ header := "", opts := opts }]
  maxRecDepth := maxRecDepth.get opts
}

/- Linters should be loadable as plugins, so store in a global IO ref instead of an attribute managed by the
    environment (which only contains `import`ed objects). -/
builtin_initialize lintersRef : IO.Ref (Array Linter) ← IO.mkRef #[]

def addLinter (l : Linter) : IO Unit := do
  let ls ← lintersRef.get
  lintersRef.set (ls.push l)

instance : MonadInfoTree CommandElabM where
  getInfoState      := return (← get).infoState
  modifyInfoState f := modify fun s => { s with infoState := f s.infoState }

instance : MonadEnv CommandElabM where
  getEnv := do pure (← get).env
  modifyEnv f := modify fun s => { s with env := f s.env }

instance : MonadOptions CommandElabM where
  getOptions := do pure (← get).scopes.head!.opts

protected def getRef : CommandElabM Syntax :=
  return (← read).ref

instance : AddMessageContext CommandElabM where
  addMessageContext := addMessageContextPartial

instance : MonadRef CommandElabM where
  getRef := Command.getRef
  withRef ref x := withReader (fun ctx => { ctx with ref := ref }) x

instance : AddErrorMessageContext CommandElabM where
  add ref msg := do
    let ctx ← read
    let ref := getBetterRef ref ctx.macroStack
    let msg ← addMessageContext msg
    let msg ← addMacroStack msg ctx.macroStack
    return (ref, msg)

def mkMessageAux (ctx : Context) (ref : Syntax) (msgData : MessageData) (severity : MessageSeverity) : Message :=
  mkMessageCore ctx.fileName ctx.fileMap msgData severity (ref.getPos?.getD ctx.cmdPos)

private def mkCoreContext (ctx : Context) (s : State) (heartbeats : Nat) : Core.Context :=
  let scope        := s.scopes.head!
  { options        := scope.opts
    currRecDepth   := ctx.currRecDepth
    maxRecDepth    := s.maxRecDepth
    ref            := ctx.ref
    currNamespace  := scope.currNamespace
    openDecls      := scope.openDecls
    initHeartbeats := heartbeats }

def liftCoreM {α} (x : CoreM α) : CommandElabM α := do
  let s ← get
  let ctx ← read
  let heartbeats ← IO.getNumHeartbeats (ε := Exception)
  let Eα := Except Exception α
  let x : CoreM Eα := try let a ← x; pure <| Except.ok a catch ex => pure <| Except.error ex
  let x : EIO Exception (Eα × Core.State) := (ReaderT.run x (mkCoreContext ctx s heartbeats)).run { env := s.env, ngen := s.ngen }
  let (ea, coreS) ← liftM x
  modify fun s => { s with env := coreS.env, ngen := coreS.ngen }
  match ea with
  | Except.ok a    => pure a
  | Except.error e => throw e

private def ioErrorToMessage (ctx : Context) (ref : Syntax) (err : IO.Error) : Message :=
  let ref := getBetterRef ref ctx.macroStack
  mkMessageAux ctx ref (toString err) MessageSeverity.error

@[inline] def liftEIO {α} (x : EIO Exception α) : CommandElabM α := liftM x

@[inline] def liftIO {α} (x : IO α) : CommandElabM α := do
  IO.toEIO (fun (ex : IO.Error) => Exception.error (← read).ref ex.toString) x

instance : MonadLiftT IO CommandElabM where
  monadLift := liftIO

def getScope : CommandElabM Scope := do pure (← get).scopes.head!

instance : MonadResolveName CommandElabM where
  getCurrNamespace := return (← getScope).currNamespace
  getOpenDecls     := return (← getScope).openDecls

instance : MonadLog CommandElabM where
  getRef      := getRef
  getFileMap  := return (← read).fileMap
  getFileName := return (← read).fileName
  logMessage msg := do
    let currNamespace ← getCurrNamespace
    let openDecls ← getOpenDecls
    let msg := { msg with data := MessageData.withNamingContext { currNamespace := currNamespace, openDecls := openDecls } msg.data }
    modify fun s => { s with messages := s.messages.add msg }

def runLinters (stx : Syntax) : CommandElabM Unit := do
  let linters ← lintersRef.get
  unless linters.isEmpty do
    for linter in linters do
      let savedState ← get
      try
        linter stx
      catch ex =>
        logException ex
      finally
        modify fun s => { savedState with messages := s.messages }

protected def getCurrMacroScope : CommandElabM Nat  := do pure (← read).currMacroScope
protected def getMainModule     : CommandElabM Name := do pure (← getEnv).mainModule

@[inline] protected def withFreshMacroScope {α} (x : CommandElabM α) : CommandElabM α := do
  let fresh ← modifyGet (fun st => (st.nextMacroScope, { st with nextMacroScope := st.nextMacroScope + 1 }))
  withReader (fun ctx => { ctx with currMacroScope := fresh }) x

instance : MonadQuotation CommandElabM where
  getCurrMacroScope   := Command.getCurrMacroScope
  getMainModule       := Command.getMainModule
  withFreshMacroScope := Command.withFreshMacroScope

unsafe def mkCommandElabAttributeUnsafe : IO (KeyedDeclsAttribute CommandElab) :=
  mkElabAttribute CommandElab `Lean.Elab.Command.commandElabAttribute `builtinCommandElab `commandElab `Lean.Parser.Command `Lean.Elab.Command.CommandElab "command"

@[implementedBy mkCommandElabAttributeUnsafe]
constant mkCommandElabAttribute : IO (KeyedDeclsAttribute CommandElab)

builtin_initialize commandElabAttribute : KeyedDeclsAttribute CommandElab ← mkCommandElabAttribute

private def elabCommandUsing (s : State) (stx : Syntax) : List CommandElab → CommandElabM Unit
  | []                => throwError "unexpected syntax{indentD stx}"
  | (elabFn::elabFns) =>
    catchInternalId unsupportedSyntaxExceptionId
      (elabFn stx)
      (fun _ => do set s; elabCommandUsing s stx elabFns)

/- Elaborate `x` with `stx` on the macro stack -/
@[inline] def withMacroExpansion {α} (beforeStx afterStx : Syntax) (x : CommandElabM α) : CommandElabM α :=
  withReader (fun ctx => { ctx with macroStack := { before := beforeStx, after := afterStx } :: ctx.macroStack }) x

instance : MonadMacroAdapter CommandElabM where
  getCurrMacroScope := getCurrMacroScope
  getNextMacroScope := return (← get).nextMacroScope
  setNextMacroScope next := modify fun s => { s with nextMacroScope := next }

instance : MonadRecDepth CommandElabM where
  withRecDepth d x := withReader (fun ctx => { ctx with currRecDepth := d }) x
  getRecDepth      := return (← read).currRecDepth
  getMaxRecDepth   := return (← get).maxRecDepth

@[inline] def withLogging (x : CommandElabM Unit) : CommandElabM Unit :=
  try
    x
  catch ex => match ex with
    | Exception.error _ _     => logException ex
    | Exception.internal id _ =>
      if isAbortExceptionId id then
        pure ()
      else
        let idName ← liftIO <| id.getName;
        logError m!"internal exception {idName}"

builtin_initialize registerTraceClass `Elab.command

partial def elabCommand (stx : Syntax) : CommandElabM Unit :=
  let mkInfoTree := do
    let ctx ← read
    let s ← get
    let scope := s.scopes.head!
    pure fun trees =>
      let tree := InfoTree.node (Info.ofCommandInfo { stx := stx }) trees
      InfoTree.context {
        env := s.env, fileMap := ctx.fileMap, mctx := {}, currNamespace := scope.currNamespace, openDecls := scope.openDecls, options := scope.opts
      } tree
  withInfoTreeContext (mkInfoTree := mkInfoTree) <| withLogging <| withRef stx <| withIncRecDepth <| withFreshMacroScope do
    runLinters stx
    match stx with
    | Syntax.node k args =>
      if k == nullKind then
        -- list of commands => elaborate in order
        -- The parser will only ever return a single command at a time, but syntax quotations can return multiple ones
        args.forM elabCommand
      else do
        trace `Elab.command fun _ => stx;
        let s ← get
        let stxNew? ← catchInternalId unsupportedSyntaxExceptionId
          (do let newStx ← adaptMacro (getMacros s.env) stx; pure (some newStx))
          (fun ex => pure none)
        match stxNew? with
        | some stxNew => withMacroExpansion stx stxNew <| elabCommand stxNew
        | _ =>
          let table := (commandElabAttribute.ext.getState s.env).table;
          let k := stx.getKind;
          match table.find? k with
          | some elabFns => elabCommandUsing s stx elabFns
          | none         => throwError "elaboration function for '{k}' has not been implemented"
    | _ => throwError "unexpected command"

/-- Adapt a syntax transformation to a regular, command-producing elaborator. -/
def adaptExpander (exp : Syntax → CommandElabM Syntax) : CommandElab := fun stx => do
  let stx' ← exp stx
  withMacroExpansion stx stx' <| elabCommand stx'

private def getVarDecls (s : State) : Array Syntax :=
  s.scopes.head!.varDecls

instance {α} : Inhabited (CommandElabM α) where
  default := throw arbitrary

private def mkMetaContext : Meta.Context := {
  config := { foApprox := true, ctxApprox := true, quasiPatternApprox := true }
}

def getBracketedBinderIds : Syntax → Array Name
  | `(bracketedBinder|($ids* $[: $ty?]? $(annot?)?)) => ids.map Syntax.getId
  | `(bracketedBinder|{$ids* $[: $ty?]?})            => ids.map Syntax.getId
  | `(bracketedBinder|[$id : $ty])                   => #[id.getId]
  | `(bracketedBinder|[$ty])                         => #[]
  | _                                                => unreachable!

private def mkTermContext (ctx : Context) (s : State) (declName? : Option Name) : Term.Context := do
  let scope      := s.scopes.head!
  let mut sectionVars := {}
  for id in scope.varDecls.concatMap getBracketedBinderIds, uid in scope.varUIds do
    sectionVars := sectionVars.insert id uid
  { macroStack     := ctx.macroStack
    fileName       := ctx.fileName
    fileMap        := ctx.fileMap
    currMacroScope := ctx.currMacroScope
    declName?      := declName?
    sectionVars    := sectionVars }

private def mkTermState (scope : Scope) (s : State) : Term.State := {
  messages          := {}
  levelNames        := scope.levelNames
  infoState.enabled := s.infoState.enabled
}

private def addTraceAsMessages (ctx : Context) (log : MessageLog) (traceState : TraceState) : MessageLog :=
  traceState.traces.foldl (init := log) fun (log : MessageLog) traceElem =>
      let ref := replaceRef traceElem.ref ctx.ref;
      let pos := ref.getPos?.getD 0;
      log.add (mkMessageCore ctx.fileName ctx.fileMap traceElem.msg MessageSeverity.information pos)

def liftTermElabM {α} (declName? : Option Name) (x : TermElabM α) : CommandElabM α := do
  let ctx ← read
  let s   ← get
  let heartbeats ← IO.getNumHeartbeats (ε := Exception)
  -- dbg_trace "heartbeats: {heartbeats}"
  let scope := s.scopes.head!
  -- We execute `x` with an empty message log. Thus, `x` cannot modify/view messages produced by previous commands.
  -- This is useful for implementing `runTermElabM` where we use `Term.resetMessageLog`
  let x : MetaM _      := (observing x).run (mkTermContext ctx s declName?) (mkTermState scope s)
  let x : CoreM _      := x.run mkMetaContext {}
  let x : EIO _ _      := x.run (mkCoreContext ctx s heartbeats) { env := s.env, ngen := s.ngen, nextMacroScope := s.nextMacroScope }
  let (((ea, termS), metaS), coreS) ← liftEIO x
  let infoTrees        := termS.infoState.trees.map fun tree =>
    let tree := tree.substitute termS.infoState.assignment
    InfoTree.context {
      env := coreS.env, fileMap := ctx.fileMap, mctx := metaS.mctx, currNamespace := scope.currNamespace, openDecls := scope.openDecls, options := scope.opts
    } tree
  modify fun s => { s with
    env             := coreS.env
    messages        := addTraceAsMessages ctx (s.messages ++ termS.messages) coreS.traceState
    nextMacroScope  := coreS.nextMacroScope
    ngen            := coreS.ngen
    infoState.trees := s.infoState.trees.append infoTrees
  }
  match ea with
  | Except.ok a     => pure a
  | Except.error ex => throw ex

@[inline] def runTermElabM {α} (declName? : Option Name) (elabFn : Array Expr → TermElabM α) : CommandElabM α := do
  let scope ← getScope
  liftTermElabM declName? <|
    -- We don't want to store messages produced when elaborating `(getVarDecls s)` because they have already been saved when we elaborated the `variable`(s) command.
    -- So, we use `Term.resetMessageLog`.
    Term.withAutoBoundImplicitLocal <|
      Term.elabBinders scope.varDecls (catchAutoBoundImplicit := true) fun xs => do
        let mut sectionFVars := {}
        for uid in scope.varUIds, x in xs do
          sectionFVars := sectionFVars.insert uid x
        withReader ({ · with sectionFVars := sectionFVars }) do
          Term.resetMessageLog
          let xs ← Term.addAutoBoundImplicits xs
          Term.withAutoBoundImplicitLocal (flag := false) <| elabFn xs

@[inline] def catchExceptions (x : CommandElabM Unit) : CommandElabCoreM Empty Unit := fun ctx ref =>
  EIO.catchExceptions (withLogging x ctx ref) (fun _ => pure ())

private def liftAttrM {α} (x : AttrM α) : CommandElabM α := do
  liftCoreM x

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

@[builtinCommandElab «namespace»] def elabNamespace : CommandElab := fun stx =>
  match stx with
  | `(namespace $n) => addNamespace n.getId
  | _               => throwUnsupportedSyntax

@[builtinCommandElab «section»] def elabSection : CommandElab := fun stx =>
  match stx with
  | `(section $header:ident) => addScopes (isNewNamespace := false) header.getId
  | `(section)               => do let currNamespace ← getCurrNamespace; addScope (isNewNamespace := false) "" currNamespace
  | _                        => throwUnsupportedSyntax

def getScopes : CommandElabM (List Scope) := do
  pure (← get).scopes

private def checkAnonymousScope : List Scope → Bool
  | { header := "", .. } :: _   => true
  | _                           => false

private def checkEndHeader : Name → List Scope → Bool
  | Name.anonymous, _                             => true
  | Name.str p s _, { header := h, .. } :: scopes => h == s && checkEndHeader p scopes
  | _,              _                             => false

private def popScopes (numScopes : Nat) : CommandElabM Unit :=
  for i in [0:numScopes] do
    popScope

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
  | none        => unless checkAnonymousScope scopes do throwError "invalid 'end', name is missing"
  | some header => unless checkEndHeader header scopes do throwError "invalid 'end', name mismatch"

@[inline] def withNamespace {α} (ns : Name) (elabFn : CommandElabM α) : CommandElabM α := do
  addNamespace ns
  let a ← elabFn
  modify fun s => { s with scopes := s.scopes.drop ns.getNumParts }
  pure a

@[specialize] def modifyScope (f : Scope → Scope) : CommandElabM Unit :=
  modify fun s => { s with
    scopes := match s.scopes with
      | h::t => f h :: t
      | []   => unreachable!
  }

def getLevelNames : CommandElabM (List Name) :=
  return (← getScope).levelNames

def addUnivLevel (idStx : Syntax) : CommandElabM Unit := withRef idStx do
  let id := idStx.getId
  let levelNames ← getLevelNames
  if levelNames.elem id then
    throwAlreadyDeclaredUniverseLevel id
  else
    modifyScope fun scope => { scope with levelNames := id :: scope.levelNames }

partial def elabChoiceAux (cmds : Array Syntax) (i : Nat) : CommandElabM Unit :=
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
  addUnivLevel n[1]

@[builtinCommandElab «universes»] def elabUniverses : CommandElab := fun n => do
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
    let declName := ns ++ id
    if env.contains declName then
      pure <| (currNamespace ++ id, declName) :: aliases
    else
      withRef idStx <| logUnknownDecl declName
      pure aliases
  modify fun s => { s with env := aliases.foldl (init := s.env) fun env p => addAlias env p.1 p.2 }

@[builtinCommandElab «open»] def elabOpen : CommandElab := fun n => do
  let openDecls ← elabOpenDecl n[1]
  modifyScope fun scope => { scope with openDecls := openDecls }

@[builtinCommandElab «variable»] def elabVariable : CommandElab
  | `(variable $binders*) => do
    -- Try to elaborate `binders` for sanity checking
    runTermElabM none fun _ => Term.withAutoBoundImplicitLocal <|
      Term.elabBinders binders (catchAutoBoundImplicit := true) fun _ => pure ()
    let varUIds ← binders.concatMap getBracketedBinderIds |>.mapM (withFreshMacroScope ∘ MonadQuotation.addMacroScope)
    modifyScope fun scope => { scope with varDecls := scope.varDecls ++ binders, varUIds := scope.varUIds ++ varUIds }
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
    let elabMetaEval : CommandElabM Unit := runTermElabM (some n) fun _ => do
      let e ← Term.elabTerm term none
      Term.synthesizeSyntheticMVarsNoPostponing
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
      let e ← Term.elabTerm term none
      let e := mkSimpleThunk e
      Term.synthesizeSyntheticMVarsNoPostponing
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

def expandDeclId (declId : Syntax) (modifiers : Modifiers) : CommandElabM ExpandDeclIdResult := do
  let currNamespace ← getCurrNamespace
  let currLevelNames ← getLevelNames
  Lean.Elab.expandDeclId currNamespace currLevelNames declId modifiers

end Elab.Command

export Elab.Command (Linter addLinter)

end Lean
