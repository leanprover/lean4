/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Alias
import Lean.Elab.Log
import Lean.Elab.ResolveName
import Lean.Elab.Term
import Lean.Elab.Binders
import Lean.Elab.SyntheticMVars
import Lean.Elab.DeclModifiers

namespace Lean
namespace Elab
namespace Command

structure Scope :=
(kind          : String)
(header        : String)
(opts          : Options := {})
(currNamespace : Name := Name.anonymous)
(openDecls     : List OpenDecl := [])
(levelNames    : List Name := [])
(varDecls      : Array Syntax := #[])

instance Scope.inhabited : Inhabited Scope := ⟨{ kind := "", header := "" }⟩

structure State :=
(env            : Environment)
(messages       : MessageLog := {})
(scopes         : List Scope := [{ kind := "root", header := "" }])
(nextMacroScope : Nat := firstFrontendMacroScope + 1)
(maxRecDepth    : Nat)
(nextInstIdx    : Nat := 1) -- for generating anonymous instance names
(ngen           : NameGenerator := {})

instance State.inhabited : Inhabited State := ⟨{ env := arbitrary _, maxRecDepth := 0 }⟩

def mkState (env : Environment) (messages : MessageLog := {}) (opts : Options := {}) : State :=
{ env := env, messages := messages, scopes := [{ kind := "root", header := "", opts := opts }], maxRecDepth := getMaxRecDepth opts }

structure Context :=
(fileName       : String)
(fileMap        : FileMap)
(currRecDepth   : Nat := 0)
(cmdPos         : String.Pos := 0)
(macroStack     : MacroStack := [])
(currMacroScope : MacroScope := firstFrontendMacroScope)
(ref            : Syntax := Syntax.missing)

abbrev CommandElabCoreM (ε) := ReaderT Context $ StateRefT State $ EIO ε
abbrev CommandElabM := CommandElabCoreM Exception
abbrev CommandElab  := Syntax → CommandElabM Unit

instance : MonadEnv CommandElabM :=
{ getEnv    := do s ← get; pure s.env,
  modifyEnv := fun f => modify fun s => { s with env := f s.env } }

instance : MonadOptions CommandElabM :=
{ getOptions := do s ← get; pure s.scopes.head!.opts }

protected def getRef : CommandElabM Syntax :=
do ctx ← read; pure ctx.ref

instance : AddMessageContext CommandElabM :=
{ addMessageContext := addMessageContextPartial }

instance : Ref CommandElabM :=
{ getRef     := Command.getRef,
  withRef    := fun α ref x => adaptReader (fun (ctx : Context) => { ctx with ref := ref }) x }

instance : AddErrorMessageContext CommandElabM :=
{ add := fun ref msg => do
  ctx ← read;
  let ref := getBetterRef ref ctx.macroStack;
  msg ← addMessageContext msg;
  msg ← addMacroStack msg ctx.macroStack;
  pure (ref, msg) }

def mkMessageAux (ctx : Context) (ref : Syntax) (msgData : MessageData) (severity : MessageSeverity) : Message :=
mkMessageCore ctx.fileName ctx.fileMap msgData severity (ref.getPos.getD ctx.cmdPos)

private def mkCoreContext (ctx : Context) (s : State) : Core.Context :=
let scope      := s.scopes.head!;
{ options      := scope.opts,
  currRecDepth := ctx.currRecDepth,
  maxRecDepth  := s.maxRecDepth,
  ref          := ctx.ref }

def liftCoreM {α} (x : CoreM α) : CommandElabM α := do
s ← get;
ctx ← read;
let Eα := Except Exception α;
let x : CoreM Eα := catch (do a ← x; pure $ Except.ok a) (fun ex => pure $ Except.error ex);
let x : EIO Exception (Eα × Core.State) := (ReaderT.run x (mkCoreContext ctx s)).run { env := s.env, ngen := s.ngen };
(ea, coreS) ← liftM x;
modify fun s => { s with env := coreS.env, ngen := coreS.ngen };
match ea with
| Except.ok a    => pure a
| Except.error e => throw e

private def ioErrorToMessage (ctx : Context) (ref : Syntax) (err : IO.Error) : Message :=
let ref := getBetterRef ref ctx.macroStack;
mkMessageAux ctx ref (toString err) MessageSeverity.error

@[inline] def liftEIO {α} (x : EIO Exception α) : CommandElabM α :=
liftM x

@[inline] def liftIO {α} (x : IO α) : CommandElabM α := do
ctx ← read;
liftEIO $ adaptExcept (fun (ex : IO.Error) => Exception.error ctx.ref ex.toString) x

instance : MonadIO CommandElabM :=
{ liftIO := fun α => liftIO }

def getScope : CommandElabM Scope := do s ← get; pure s.scopes.head!

def getCurrNamespace : CommandElabM Name := do
scope ← getScope; pure scope.currNamespace

def getOpenDecls : CommandElabM (List OpenDecl) := do
scope ← getScope; pure scope.openDecls

instance CommandElabM.monadLog : MonadLog CommandElabM :=
{ getRef      := getRef,
  getFileMap  := do ctx ← read; pure ctx.fileMap,
  getFileName := do ctx ← read; pure ctx.fileName,
  logMessage  := fun msg => do
    currNamespace ← getCurrNamespace;
    openDecls ← getOpenDecls;
    let msg := { msg with data := MessageData.withNamingContext { currNamespace := currNamespace, openDecls := openDecls } msg.data };
    modify $ fun s => { s with messages := s.messages.add msg } }

protected def getCurrMacroScope : CommandElabM Nat  := do ctx ← read; pure ctx.currMacroScope
protected def getMainModule     : CommandElabM Name := do env ← getEnv; pure env.mainModule

@[inline] protected def withFreshMacroScope {α} (x : CommandElabM α) : CommandElabM α := do
fresh ← modifyGet (fun st => (st.nextMacroScope, { st with nextMacroScope := st.nextMacroScope + 1 }));
adaptReader (fun (ctx : Context) => { ctx with currMacroScope := fresh }) x

instance CommandElabM.MonadQuotation : MonadQuotation CommandElabM := {
  getCurrMacroScope   := Command.getCurrMacroScope,
  getMainModule       := Command.getMainModule,
  withFreshMacroScope := @Command.withFreshMacroScope
}

unsafe def mkCommandElabAttribute : IO (KeyedDeclsAttribute CommandElab) :=
mkElabAttribute CommandElab `Lean.Elab.Command.commandElabAttribute `builtinCommandElab `commandElab `Lean.Parser.Command `Lean.Elab.Command.CommandElab "command"
@[init mkCommandElabAttribute] constant commandElabAttribute : KeyedDeclsAttribute CommandElab := arbitrary _

private def elabCommandUsing (s : State) (stx : Syntax) : List CommandElab → CommandElabM Unit
| []                => do
  let refFmt := stx.prettyPrint;
  throwError ("unexpected syntax" ++ MessageData.nest 2 (Format.line ++ refFmt))
| (elabFn::elabFns) => catchInternalId unsupportedSyntaxExceptionId (elabFn stx)
  (fun _ => do set s; elabCommandUsing elabFns)

/- Elaborate `x` with `stx` on the macro stack -/
@[inline] def withMacroExpansion {α} (beforeStx afterStx : Syntax) (x : CommandElabM α) : CommandElabM α :=
adaptReader (fun (ctx : Context) => { ctx with macroStack := { before := beforeStx, after := afterStx } :: ctx.macroStack }) x

instance : MonadMacroAdapter CommandElabM :=
{ getCurrMacroScope := getCurrMacroScope,
  getNextMacroScope := do s ← get; pure s.nextMacroScope,
  setNextMacroScope := fun next => modify $ fun s => { s with nextMacroScope := next } }

instance : MonadRecDepth CommandElabM :=
{ withRecDepth   := fun α d x => adaptReader (fun (ctx : Context) => { ctx with currRecDepth := d }) x,
  getRecDepth    := do ctx ← read; pure ctx.currRecDepth,
  getMaxRecDepth := do s ← get; pure s.maxRecDepth }

@[inline] def withLogging (x : CommandElabM Unit) : CommandElabM Unit :=
catch x
  (fun ex => match ex with
    | Exception.error _ _   => logException ex
    | Exception.internal id =>
      if id == abortExceptionId then
        pure ()
      else do
        idName ← liftIO $ id.getName;
        logError ("internal exception " ++ toString idName))

partial def elabCommand : Syntax → CommandElabM Unit
| stx => withRef stx $ withIncRecDepth $ withFreshMacroScope $ withLogging $ match stx with
  | Syntax.node k args =>
    if k == nullKind then
      -- list of commands => elaborate in order
      -- The parser will only ever return a single command at a time, but syntax quotations can return multiple ones
      args.forM elabCommand
    else do
      trace `Elab.step fun _ => stx;
      s ← get;
      stxNew? ← catchInternalId unsupportedSyntaxExceptionId
        (do newStx ← adaptMacro (getMacros s.env) stx; pure (some newStx))
        (fun ex => pure none);
      match stxNew? with
      | some stxNew => withMacroExpansion stx stxNew $ elabCommand stxNew
      | _ => do
        let table := (commandElabAttribute.ext.getState s.env).table;
        let k := stx.getKind;
        match table.find? k with
        | some elabFns => elabCommandUsing s stx elabFns
        | none         => throwError ("elaboration function for '" ++ toString k ++ "' has not been implemented")
  | _ => throwError "unexpected command"

/-- Adapt a syntax transformation to a regular, command-producing elaborator. -/
def adaptExpander (exp : Syntax → CommandElabM Syntax) : CommandElab :=
fun stx => do
  stx' ← exp stx;
  withMacroExpansion stx stx' $ elabCommand stx'

private def getVarDecls (s : State) : Array Syntax :=
s.scopes.head!.varDecls

instance CommandElabM.inhabited {α} : Inhabited (CommandElabM α) :=
⟨throw $ arbitrary _⟩

private def mkMetaContext : Meta.Context :=
{ config := { foApprox := true, ctxApprox := true, quasiPatternApprox := true } }

private def mkTermContext (ctx : Context) (s : State) (declName? : Option Name) : Term.Context :=
let scope      := s.scopes.head!;
{
  macroStack     := ctx.macroStack,
  fileName       := ctx.fileName,
  fileMap        := ctx.fileMap,
  currMacroScope := ctx.currMacroScope,
  currNamespace  := scope.currNamespace,
  levelNames     := scope.levelNames,
  openDecls      := scope.openDecls,
  declName?      := declName?
}

/-- Auxiliary function for `liftMetaM` -/
private def mkMessageAux (ref : Syntax) (ctx : Context) (msgData : MessageData) (severity : MessageSeverity) : Message :=
let pos := ref.getPos.getD 0;
mkMessageCore ctx.fileName ctx.fileMap msgData severity pos

private def addTraceAsMessages (ctx : Context) (log : MessageLog) (traceState : TraceState) : MessageLog :=
traceState.traces.foldl
  (fun (log : MessageLog) traceElem =>
    let ref := replaceRef traceElem.ref ctx.ref;
    let pos := ref.getPos.getD 0;
    log.add (mkMessageCore ctx.fileName ctx.fileMap traceElem.msg MessageSeverity.information pos))
  log

def liftTermElabM {α} (declName? : Option Name) (x : TermElabM α) : CommandElabM α := do
ctx ← read;
s   ← get;
let scope := s.scopes.head!;
-- We execute `x` with an empty message log. Thus, `x` cannot modify/view messages produced by previous commands.
-- This is useful for implementing `runTermElabM` where we use `Term.resetMessageLog`
let messages         := s.messages;
let x : MetaM _      := (observing x).run (mkTermContext ctx s declName?) { messages := {}, nextMacroScope := s.nextMacroScope };
let x : CoreM _      := x.run mkMetaContext {};
let x : EIO _ _      := x.run (mkCoreContext ctx s) { env := s.env, ngen := s.ngen };
(((ea, termS), _), coreS) ← liftEIO x;
modify fun s => { s with env := coreS.env, messages := addTraceAsMessages ctx (messages ++ termS.messages) coreS.traceState, ngen := coreS.ngen };
match ea with
| Except.ok a     => pure a
| Except.error ex => throw ex

@[inline] def runTermElabM {α} (declName? : Option Name) (elabFn : Array Expr → TermElabM α) : CommandElabM α := do
s ← get;
liftTermElabM declName?
  -- We don't want to store messages produced when elaborating `(getVarDecls s)` because they have already been saved when we elaborated the `variable`(s) command.
  -- So, we use `Term.resetMessageLog`.
  (Term.elabBinders (getVarDecls s) (fun xs => do Term.resetMessageLog; elabFn xs))

@[inline] def catchExceptions (x : CommandElabM Unit) : CommandElabCoreM Empty Unit :=
fun ctx ref => EIO.catchExceptions (withLogging x ctx ref) (fun _ => pure ())

private def addScope (kind : String) (header : String) (newNamespace : Name) : CommandElabM Unit :=
modify $ fun s => {
  s with
  env    := s.env.registerNamespace newNamespace,
  scopes := { s.scopes.head! with kind := kind, header := header, currNamespace := newNamespace } :: s.scopes
}

private def addScopes (kind : String) (updateNamespace : Bool) : Name → CommandElabM Unit
| Name.anonymous => pure ()
| Name.str p header _ => do
  addScopes p;
  currNamespace ← getCurrNamespace;
  addScope kind header (if updateNamespace then currNamespace ++ header else currNamespace)
| _ => throwError "invalid scope"

private def addNamespace (header : Name) : CommandElabM Unit :=
addScopes "namespace" true header

@[builtinCommandElab «namespace»] def elabNamespace : CommandElab :=
fun stx => match_syntax stx with
  | `(namespace $n) => addNamespace n.getId
  | _               => throwUnsupportedSyntax

@[builtinCommandElab «section»] def elabSection : CommandElab :=
fun stx => match_syntax stx with
  | `(section $header:ident) => addScopes "section" false header.getId
  | `(section)               => do currNamespace ← getCurrNamespace; addScope "section" "" currNamespace
  | _                        => throwUnsupportedSyntax

def getScopes : CommandElabM (List Scope) := do
s ← get; pure s.scopes

private def checkAnonymousScope : List Scope → Bool
| { header := "", .. } :: _   => true
| _                           => false

private def checkEndHeader : Name → List Scope → Bool
| Name.anonymous, _                             => true
| Name.str p s _, { header := h, .. } :: scopes => h == s && checkEndHeader p scopes
| _,              _                             => false

@[builtinCommandElab «end»] def elabEnd : CommandElab :=
fun stx => do
  let header? := (stx.getArg 1).getOptionalIdent?;
  let endSize := match header? with
    | none   => 1
    | some n => n.getNumParts;
  scopes ← getScopes;
  if endSize < scopes.length then
    modify $ fun s => { s with scopes := s.scopes.drop endSize }
  else do {
    -- we keep "root" scope
    modify $ fun s => { s with scopes := s.scopes.drop (s.scopes.length - 1) };
    throwError "invalid 'end', insufficient scopes"
  };
  match header? with
  | none        => unless (checkAnonymousScope scopes) $ throwError "invalid 'end', name is missing"
  | some header => unless (checkEndHeader header scopes) $ throwError "invalid 'end', name mismatch"

@[inline] def withNamespace {α} (ns : Name) (elabFn : CommandElabM α) : CommandElabM α := do
addNamespace ns;
a ← elabFn;
modify $ fun s => { s with scopes := s.scopes.drop ns.getNumParts };
pure a

@[specialize] def modifyScope (f : Scope → Scope) : CommandElabM Unit :=
modify $ fun s =>
  { s with
    scopes := match s.scopes with
    | h::t => f h :: t
    | []   => unreachable! }

def getLevelNames : CommandElabM (List Name) := do
scope ← getScope; pure scope.levelNames

def addUnivLevel (idStx : Syntax) : CommandElabM Unit :=
withRef idStx do
let id := idStx.getId;
levelNames ← getLevelNames;
if levelNames.elem id then
  throwAlreadyDeclaredUniverseLevel id
else
  modifyScope $ fun scope => { scope with levelNames := id :: scope.levelNames }

partial def elabChoiceAux (cmds : Array Syntax) : Nat → CommandElabM Unit
| i =>
  if h : i < cmds.size then
    let cmd := cmds.get ⟨i, h⟩;
    catchInternalId unsupportedSyntaxExceptionId
      (elabCommand cmd)
      (fun ex => elabChoiceAux (i+1))
  else
    throwUnsupportedSyntax

@[builtinCommandElab choice] def elbChoice : CommandElab :=
fun stx => elabChoiceAux stx.getArgs 0

@[builtinCommandElab «universe»] def elabUniverse : CommandElab :=
fun n => do
  addUnivLevel (n.getArg 1)

@[builtinCommandElab «universes»] def elabUniverses : CommandElab :=
fun n => do
  let idsStx := n.getArg 1;
  idsStx.forArgsM addUnivLevel

@[builtinCommandElab «init_quot»] def elabInitQuot : CommandElab :=
fun stx => do
  env ← getEnv;
  match env.addDecl Declaration.quotDecl with
  | Except.ok env   => setEnv env
  | Except.error ex => do
    opts ← getOptions;
    throwError (ex.toMessageData opts)

def logUnknownDecl (declName : Name) : CommandElabM Unit :=
logError ("unknown declaration '" ++ toString declName ++ "'")

def resolveNamespace (id : Name) : CommandElabM Name := do
env           ← getEnv;
currNamespace ← getCurrNamespace;
openDecls ← getOpenDecls;
match Elab.resolveNamespace env currNamespace openDecls id with
| some ns => pure ns
| none    => throwUnsupportedSyntax

@[builtinCommandElab «export»] def elabExport : CommandElab :=
fun stx => do
  -- `stx` is of the form (Command.export "export" <namespace> "(" (null <ids>*) ")")
  let id  := stx.getIdAt 1;
  ns ← resolveNamespace id;
  currNamespace ← getCurrNamespace;
  when (ns == currNamespace) $ throwError "invalid 'export', self export";
  env ← getEnv;
  let ids := (stx.getArg 3).getArgs;
  aliases ← ids.foldlM
   (fun (aliases : List (Name × Name)) (idStx : Syntax) => do {
      let id := idStx.getId;
      let declName := ns ++ id;
      if env.contains declName then
        pure $ (currNamespace ++ id, declName) :: aliases
      else do
        withRef idStx $ logUnknownDecl declName;
        pure aliases
      })
    [];
  modify $ fun s => { s with env := aliases.foldl (fun env p => addAlias env p.1 p.2) s.env }

def addOpenDecl (d : OpenDecl) : CommandElabM Unit :=
modifyScope $ fun scope => { scope with openDecls := d :: scope.openDecls }

def elabOpenSimple (n : SyntaxNode) : CommandElabM Unit :=
-- `open` id+
let nss := n.getArg 0;
nss.forArgsM $ fun ns => do
  ns ← resolveNamespace ns.getId;
  addOpenDecl (OpenDecl.simple ns [])

-- `open` id `(` id+ `)`
def elabOpenOnly (n : SyntaxNode) : CommandElabM Unit := do
let ns  := n.getIdAt 0;
ns ← resolveNamespace ns;
let ids := n.getArg 2;
ids.forArgsM $ fun idStx => do
  let id := idStx.getId;
  let declName := ns ++ id;
  env ← getEnv;
  if env.contains declName then
    addOpenDecl (OpenDecl.explicit id declName)
  else
    withRef idStx $ logUnknownDecl declName

-- `open` id `hiding` id+
def elabOpenHiding (n : SyntaxNode) : CommandElabM Unit := do
let ns := n.getIdAt 0;
ns ← resolveNamespace ns;
let idsStx := n.getArg 2;
env ← getEnv;
ids : List Name ← idsStx.foldArgsM (fun idStx ids => do
  let id := idStx.getId;
  let declName := ns ++ id;
  if env.contains declName then
    pure (id::ids)
  else do
    withRef idStx $ logUnknownDecl declName;
    pure ids)
  [];
addOpenDecl (OpenDecl.simple ns ids)

-- `open` id `renaming` sepBy (id `->` id) `,`
def elabOpenRenaming (n : SyntaxNode) : CommandElabM Unit := do
let ns := n.getIdAt 0;
ns ← resolveNamespace ns;
let rs := (n.getArg 2);
rs.forSepArgsM $ fun stx => do
  let fromId   := stx.getIdAt 0;
  let toId     := stx.getIdAt 2;
  let declName := ns ++ fromId;
  env ← getEnv;
  if env.contains declName then
    addOpenDecl (OpenDecl.explicit toId declName)
  else
    withRef stx $ logUnknownDecl declName

@[builtinCommandElab «open»] def elabOpen : CommandElab :=
fun n => do
  let body := (n.getArg 1).asNode;
  let k    := body.getKind;
  if k == `Lean.Parser.Command.openSimple then
    elabOpenSimple body
  else if k == `Lean.Parser.Command.openOnly then
    elabOpenOnly body
  else if k == `Lean.Parser.Command.openHiding then
    elabOpenHiding body
  else
    elabOpenRenaming body

@[builtinCommandElab «variable»] def elabVariable : CommandElab :=
fun n => do
  -- `variable` bracketedBinder
  let binder := n.getArg 1;
  -- Try to elaborate `binder` for sanity checking
  runTermElabM none $ fun _ => Term.elabBinder binder $ fun _ => pure ();
  modifyScope $ fun scope => { scope with varDecls := scope.varDecls.push binder }

@[builtinCommandElab «variables»] def elabVariables : CommandElab :=
fun n => do
  -- `variables` bracketedBinder+
  let binders := (n.getArg 1).getArgs;
  -- Try to elaborate `binders` for sanity checking
  runTermElabM none $ fun _ => Term.elabBinders binders $ fun _ => pure ();
  modifyScope $ fun scope => { scope with varDecls := scope.varDecls ++ binders }

@[inline] def withoutModifyingEnv {α} (x : CommandElabM α) : CommandElabM α := do
env ← getEnv;
finally x (setEnv env)

open Meta

@[builtinCommandElab Lean.Parser.Command.check] def elabCheck : CommandElab :=
fun stx => do
  let term := stx.getArg 1;
  withoutModifyingEnv $ runTermElabM (some `_check) $ fun _ => do
    e    ← Term.elabTerm term none;
    Term.synthesizeSyntheticMVarsNoPostponing;
    type ← inferType e;
    logInfo (e ++ " : " ++ type);
    pure ()

def hasNoErrorMessages : CommandElabM Bool := do
s ← get; pure $ !s.messages.hasErrors

def failIfSucceeds (x : CommandElabM Unit) : CommandElabM Unit := do
let resetMessages : CommandElabM MessageLog := do {
  s ← get;
  let messages := s.messages;
  modify $ fun s => { s with messages := {} };
  pure messages
};
let restoreMessages (prevMessages : MessageLog) : CommandElabM Unit := do {
  modify $ fun s => { s with messages := prevMessages ++ s.messages.errorsToWarnings }
};
prevMessages ← resetMessages;
succeeded ← finally
  (catch
     (do x; hasNoErrorMessages)
     (fun ex => match ex with
       | Exception.error _ _    => do logException ex; pure false
       | Exception.internal id  => do logError "internal"; pure false)) -- TODO: improve `logError "internal"`
  (restoreMessages prevMessages);
when succeeded $
  throwError "unexpected success"

@[builtinCommandElab «check_failure»] def elabCheckFailure : CommandElab :=
fun stx => failIfSucceeds $ elabCheck stx

unsafe def elabEvalUnsafe : CommandElab :=
fun stx => do
  let ref  := stx;
  let term := stx.getArg 1;
  let n := `_eval;
  ctx ← read;
  let addAndCompile (value : Expr) : TermElabM Unit := do {
    type ← inferType value;
    let decl := Declaration.defnDecl { name := n, lparams := [], type := type,
      value := value, hints := ReducibilityHints.opaque, isUnsafe := true };
    Term.ensureNoUnassignedMVars decl;
    addAndCompile decl
  };
  let elabMetaEval : CommandElabM Unit := runTermElabM (some n) fun _ => do {
    e ← Term.elabTerm term none;
    Term.synthesizeSyntheticMVarsNoPostponing;
    e ← withLocalDeclD `env (mkConst `Lean.Environment) fun env =>
        withLocalDeclD `opts (mkConst `Lean.Options) fun opts => do {
          e ← mkAppM `Lean.runMetaEval #[env, opts, e];
          mkLambdaFVars #[env, opts] e
        };
    env ← getEnv;
    opts ← getOptions;
    act ← finally (do addAndCompile e; evalConst (Environment → Options → IO (String × Except IO.Error Environment)) n) (setEnv env);
    (out, res) ← MonadIO.liftIO $ act env opts; -- we execute `act` using the environment
    logInfo out;
    match res with
    | Except.error e => throwError e.toString
    | Except.ok env  => do setEnv env; pure ()
  };
  let elabEval : CommandElabM Unit := runTermElabM (some n) fun _ => do {
    -- fall back to non-meta eval if MetaHasEval hasn't been defined yet
    -- modify e to `runEval e`
    e    ← Term.elabTerm term none;
    Term.synthesizeSyntheticMVarsNoPostponing;
    e ← mkAppM `Lean.runEval #[e];
    env ← getEnv;
    act ← finally (do addAndCompile e; evalConst (IO (String × Except IO.Error Unit)) n ) (setEnv env);
    (out, res) ← MonadIO.liftIO act;
    logInfo out;
    match res with
    | Except.error e => throwError e.toString
    | Except.ok _    => pure ()
  };
  env ← getEnv;
  if env.contains `Lean.MetaHasEval then do
    elabMetaEval
  else
    elabEval

@[builtinCommandElab «eval», implementedBy elabEvalUnsafe]
constant elabEval : CommandElab := arbitrary _

@[builtinCommandElab «synth»] def elabSynth : CommandElab :=
fun stx => do
  let term := stx.getArg 1;
  withoutModifyingEnv $ runTermElabM `_synth_cmd $ fun _ => do
    inst ← Term.elabTerm term none;
    Term.synthesizeSyntheticMVarsNoPostponing;
    inst ← instantiateMVars inst;
    val  ← synthInstance inst;
    logInfo val;
    pure ()

def setOption (optionName : Name) (val : DataValue) : CommandElabM Unit := do
decl ← liftIO $ getOptionDecl optionName;
unless (decl.defValue.sameCtor val) $ throwError "type mismatch at set_option";
modifyScope $ fun scope => { scope with opts := scope.opts.insert optionName val };
match optionName, val with
| `maxRecDepth, DataValue.ofNat max => modify $ fun s => { s with maxRecDepth := max }
| _,            _                   => pure ()

@[builtinCommandElab «set_option»] def elabSetOption : CommandElab :=
fun stx => do
  let optionName := stx.getIdAt 1;
  let val        := stx.getArg 2;
  match val.isStrLit? with
  | some str => setOption optionName (DataValue.ofString str)
  | none     =>
  match val.isNatLit? with
  | some num => setOption optionName (DataValue.ofNat num)
  | none     =>
  match val with
  | Syntax.atom _ "true"  => setOption optionName (DataValue.ofBool true)
  | Syntax.atom _ "false" => setOption optionName (DataValue.ofBool false)
  | _ => logErrorAt val ("unexpected set_option value " ++ toString val)

@[builtinMacro Lean.Parser.Command.«in»] def expandInCmd : Macro :=
fun stx => do
  let cmd₁ := stx.getArg 0;
  let cmd₂ := stx.getArg 2;
  `(section $cmd₁:command $cmd₂:command end)

def expandDeclId (declId : Syntax) (modifiers : Modifiers) : CommandElabM ExpandDeclIdResult := do
currNamespace ← getCurrNamespace;
currLevelNames ← getLevelNames;
Lean.Elab.expandDeclId currNamespace currLevelNames declId modifiers

end Command
end Elab
end Lean
