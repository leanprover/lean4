/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Init.Control.StateRef
import Lean.Elab.Alias
import Lean.Elab.Log
import Lean.Elab.ResolveName
import Lean.Elab.Term
import Lean.Elab.Binders
import Lean.Elab.SyntheticMVars

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

instance Exception.inhabited : Inhabited Exception := ⟨Exception.error $ arbitrary _⟩

abbrev CommandElabCoreM (ε) := ReaderT Context $ StateRefT State $ EIO ε
abbrev CommandElabM := CommandElabCoreM Exception
abbrev CommandElab  := Syntax → CommandElabM Unit

def mkMessageAux (ctx : Context) (ref : Syntax) (msgData : MessageData) (severity : MessageSeverity) : Message :=
mkMessageCore ctx.fileName ctx.fileMap msgData severity (ref.getPos.getD ctx.cmdPos)

private def mkCoreContext (ctx : Context) (s : State) : Core.Context :=
let scope      := s.scopes.head!;
{ options      := scope.opts,
  currRecDepth := ctx.currRecDepth,
  maxRecDepth  := s.maxRecDepth,
  ref          := ctx.ref }

def fromCoreException (ctx : Context) (ex : Core.Exception) : Exception :=
match ex with
| Core.Exception.error ref msg  => Exception.error (mkMessageAux ctx (replaceRef ref ctx.ref) msg MessageSeverity.error)
| Core.Exception.io error       => Exception.io error
| Core.Exception.kernel ex opts => Exception.error (mkMessageAux ctx ctx.ref (ex.toMessageData opts) MessageSeverity.error)

def liftCoreM {α} (x : CoreM α) : CommandElabM α := do
s ← get;
ctx ← read;
let Eα := Except Core.Exception α;
let x : CoreM Eα := catch (do a ← x; pure $ Except.ok a) (fun ex => pure $ Except.error ex);
let x : EIO Core.Exception (Eα × Core.State) := (ReaderT.run x (mkCoreContext ctx s)).run { env := s.env, ngen := s.ngen };
let x : EIO Exception (Eα × Core.State) := adaptExcept (fromCoreException ctx) x;
(ea, coreS) ← liftM x;
modify fun s => { s with env := coreS.env, ngen := coreS.ngen };
match ea with
| Except.ok a    => pure a
| Except.error e => throw (fromCoreException ctx e)

@[inline] def getCurrRef : CommandElabM Syntax := do
ctx ← read;
pure ctx.ref

/- Execute `x` using using `ref` as the default Syntax for providing position information to error messages. -/
@[inline] def withRef {α} (ref : Syntax) (x : CommandElabM α) : CommandElabM α := do
adaptReader (fun (ctx : Context) => { ctx with ref := replaceRef ref ctx.ref }) x


private def ioErrorToMessage (ctx : Context) (ref : Syntax) (err : IO.Error) : Message :=
let ref := getBetterRef ref ctx.macroStack;
mkMessageAux ctx ref (addMacroStack (toString err) ctx.macroStack) MessageSeverity.error

-- This instance is needed for StateRefT
instance monadIOAux : MonadIO (EIO Exception) :=
{ liftIO := fun _ x => adaptExcept (fun ex => Exception.error { fileName := "<unavaiable>", pos := ⟨0, 0⟩, data := toString ex }) x }

@[inline] def liftEIO {α} (x : EIO Exception α) : CommandElabM α :=
liftM x

@[inline] def liftIO {α} (x : IO α) : CommandElabM α := do
ctx ← read;
liftEIO $ adaptExcept (fun ex => Exception.error $ ioErrorToMessage ctx ctx.ref ex) x

instance : MonadIO CommandElabM :=
{ liftIO := fun α => liftIO }

def getEnv : CommandElabM Environment := do s ← get; pure s.env
def getScope : CommandElabM Scope := do s ← get; pure s.scopes.head!
def getOptions : CommandElabM Options := do scope ← getScope; pure scope.opts

def addContext (msg : MessageData) : CommandElabM MessageData := do
env ← getEnv; opts ← getOptions;
pure (MessageData.withContext { env := env, mctx := {}, lctx := {}, opts := opts } msg)

instance CommandElabM.monadLog : MonadLog CommandElabM :=
{ getRef      := do ctx ← read; pure ctx.ref,
  getFileMap  := do ctx ← read; pure ctx.fileMap,
  getFileName := do ctx ← read; pure ctx.fileName,
  addContext  := addContext,
  logMessage  := fun msg => modify $ fun s => { s with messages := s.messages.add msg } }

/--
  Throws an error with the given `msgData` and extracting position information from `ref`.
  If `ref` does not contain position information, then use `cmdPos` -/
def throwError {α} (msgData : MessageData) : CommandElabM α := do
ctx ← read;
let ref     := getBetterRef ctx.ref ctx.macroStack;
let msgData := addMacroStack msgData ctx.macroStack;
withRef ref do
  msg ← mkMessage msgData MessageSeverity.error;
  throw (Exception.error msg)

def throwErrorAt {α} (ref : Syntax) (msgData : MessageData) : CommandElabM α :=
withRef ref $ throwError msgData

def logTrace (cls : Name) (msg : MessageData) : CommandElabM Unit := do
msg ← addContext $ MessageData.tagged cls msg;
logInfo msg

@[inline] def trace (cls : Name) (msg : Unit → MessageData) : CommandElabM Unit := do
opts ← getOptions;
when (checkTraceOption opts cls) $ logTrace cls (msg ())

def throwUnsupportedSyntax {α} : CommandElabM α :=
throw Elab.Exception.unsupportedSyntax

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

@[inline] def withIncRecDepth {α} (x : CommandElabM α) : CommandElabM α := do
ctx ← read; s ← get;
when (ctx.currRecDepth == s.maxRecDepth) $ throwError maxRecDepthErrorMessage;
adaptReader (fun (ctx : Context) => { ctx with currRecDepth := ctx.currRecDepth + 1 }) x

private def elabCommandUsing (s : State) (stx : Syntax) : List CommandElab → CommandElabM Unit
| []                => do
  let refFmt := stx.prettyPrint;
  throwError ("unexpected syntax" ++ MessageData.nest 2 (Format.line ++ refFmt))
| (elabFn::elabFns) => catch (elabFn stx)
  (fun ex => match ex with
    | Exception.error _           => throw ex
    | Exception.io _              => throw ex
    | Exception.unsupportedSyntax => do set s; elabCommandUsing elabFns)

/- Elaborate `x` with `stx` on the macro stack -/
@[inline] def withMacroExpansion {α} (beforeStx afterStx : Syntax) (x : CommandElabM α) : CommandElabM α :=
adaptReader (fun (ctx : Context) => { ctx with macroStack := { before := beforeStx, after := afterStx } :: ctx.macroStack }) x

instance : MonadMacroAdapter CommandElabM :=
{ getEnv                 := getEnv,
  getCurrMacroScope      := getCurrMacroScope,
  getNextMacroScope      := do s ← get; pure s.nextMacroScope,
  setNextMacroScope      := fun next => modify $ fun s => { s with nextMacroScope := next },
  getCurrRecDepth        := do ctx ← read; pure ctx.currRecDepth,
  getMaxRecDepth         := do s ← get; pure s.maxRecDepth,
  throwError             := @throwErrorAt,
  throwUnsupportedSyntax := @throwUnsupportedSyntax}

partial def elabCommand : Syntax → CommandElabM Unit
| stx => withRef stx $ withIncRecDepth $ withFreshMacroScope $ match stx with
  | Syntax.node k args =>
    if k == nullKind then
      -- list of commands => elaborate in order
      -- The parser will only ever return a single command at a time, but syntax quotations can return multiple ones
      args.forM elabCommand
    else do
      trace `Elab.step fun _ => stx;
      s ← get;
      stxNew? ← catch
        (do newStx ← adaptMacro (getMacros s.env) stx; pure (some newStx))
        (fun ex => match ex with
          | Exception.unsupportedSyntax => pure none
          | _                           => throw ex);
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
{ config := { foApprox := true, ctxApprox := true, quasiPatternApprox := true, isDefEqStuckEx := true } }

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

def fromTermException (ex : Term.Exception) : Exception :=
match ex with
| Term.Exception.postpone => unreachable!
| Term.Exception.ex ex    => ex

def liftTermElabM {α} (declName? : Option Name) (x : TermElabM α) : CommandElabM α := do
ctx ← read;
s   ← get;
let scope := s.scopes.head!;
let x : EMetaM _ _      := (observing x).run (mkTermContext ctx s declName?) { messages := s.messages, nextMacroScope := s.nextMacroScope };
let x : ECoreM _ _      := x.run mkMetaContext {};
let x : EIO _ _         := x.run (mkCoreContext ctx s) { env := s.env, ngen := s.ngen };
let x : EIO Exception _ := adaptExcept fromTermException x;
(((ea, termS), _), coreS) ← liftEIO x;
modify fun s => { s with env := coreS.env, messages := termS.messages, ngen := coreS.ngen };
match ea with
| Except.ok a     => pure a
| Except.error ex => throw (fromTermException ex)

@[inline] def runTermElabM {α} (declName? : Option Name) (elabFn : Array Expr → TermElabM α) : CommandElabM α := do
s ← get; liftTermElabM declName? (Term.elabBinders (getVarDecls s) elabFn)

@[inline] def withLogging (x : CommandElabM Unit) : CommandElabM Unit :=
catch x (fun ex => match ex with
  | Exception.error ex          => do logMessage ex; pure ()
  | Exception.io _              => throw ex
  | Exception.unsupportedSyntax => unreachable!)

@[inline] def catchExceptions (x : CommandElabM Unit) : CommandElabCoreM Empty Unit :=
fun ctx ref => EIO.catchExceptions (withLogging x ctx ref) (fun _ => pure ())

def dbgTrace {α} [HasToString α] (a : α) : CommandElabM Unit :=
_root_.dbgTrace (toString a) $ fun _ => pure ()

def setEnv (newEnv : Environment) : CommandElabM Unit :=
modify $ fun s => { s with env := newEnv }

@[inline] def modifyEnv (f : Environment → Environment) : CommandElabM Unit :=
modify $ fun s => { s with env := f s.env }

def getCurrNamespace : CommandElabM Name := do
scope ← getScope; pure scope.currNamespace

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
  | _               => throw Exception.unsupportedSyntax

@[builtinCommandElab «section»] def elabSection : CommandElab :=
fun stx => match_syntax stx with
  | `(section $header:ident) => addScopes "section" false header.getId
  | `(section)               => do currNamespace ← getCurrNamespace; addScope "section" "" currNamespace
  | _                        => throw Exception.unsupportedSyntax

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

def throwAlreadyDeclaredUniverseLevel {α} (u : Name) : CommandElabM α :=
throwError ("a universe level named '" ++ toString u ++ "' has already been declared")

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
    catch
      (elabCommand cmd)
      (fun ex => match ex with
        | Exception.unsupportedSyntax => elabChoiceAux (i+1)
        | _ => throw ex)
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

def getOpenDecls : CommandElabM (List OpenDecl) := do
scope ← getScope; pure scope.openDecls

def logUnknownDecl (declName : Name) : CommandElabM Unit :=
logError ("unknown declaration '" ++ toString declName ++ "'")

def resolveNamespace (id : Name) : CommandElabM Name := do
env           ← getEnv;
currNamespace ← getCurrNamespace;
openDecls ← getOpenDecls;
match Elab.resolveNamespace env currNamespace openDecls id with
| some ns => pure ns
| none    => throw Exception.unsupportedSyntax

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

@[builtinCommandElab «check»] def elabCheck : CommandElab :=
fun stx => do
  let term := stx.getArg 1;
  withoutModifyingEnv $ runTermElabM (some `_check) $ fun _ => do
    e    ← Term.elabTerm term none;
    Term.synthesizeSyntheticMVars false;
    type ← Term.inferType e;
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
       | Exception.error msg         => do modify (fun s => { s with messages := s.messages.add msg }); pure false
       | Exception.io ex             => do logError (toString ex); pure false
       | Exception.unsupportedSyntax => do logError "unsupported syntax"; pure false))
  (restoreMessages prevMessages);
when succeeded $
  throwError "unexpected success"

@[builtinCommandElab «check_failure»] def elabCheckFailure : CommandElab :=
fun stx => failIfSucceeds $ elabCheck stx

def addDecl (decl : Declaration) : CommandElabM Unit := liftTermElabM none $ Term.addDecl decl
def compileDecl (decl : Declaration) : CommandElabM Unit := liftTermElabM none $ Term.compileDecl decl

def addInstance (declName : Name) : CommandElabM Unit := do
env ← getEnv;
env ← liftIO $ Meta.addGlobalInstance env declName;
setEnv env

unsafe def elabEvalUnsafe : CommandElab :=
fun stx => withoutModifyingEnv do
  let ref  := stx;
  let term := stx.getArg 1;
  let n := `_eval;
  ctx ← read;
  env ← getEnv;
  let addAndCompile (value : Expr) : TermElabM Unit := do {
    type ← Term.inferType value;
    let decl := Declaration.defnDecl { name := n, lparams := [], type := type,
      value := value, hints := ReducibilityHints.opaque, isUnsafe := true };
    Term.addDecl decl;
    Term.compileDecl decl
  };
  let elabMetaEval : CommandElabM Unit := do {
    act : IO Environment ← runTermElabM (some n) fun _ => do {
      e    ← Term.elabTerm term none;
      Term.synthesizeSyntheticMVars false;
        e ← Term.withLocalDecl `env BinderInfo.default (mkConst `Lean.Environment) fun env =>
          Term.withLocalDecl `opts BinderInfo.default (mkConst `Lean.Options) fun opts => do {
            e ← Term.mkAppM `Lean.MetaHasEval.eval #[env, opts, e, toExpr false];
            Term.mkLambda #[env, opts] e
          };
        addAndCompile e;
        env ← Term.getEnv;
        opts ← Term.getOptions;
        match env.evalConst (Environment → Options → IO Environment) n with
        | Except.error e => Term.throwError e
        | Except.ok act  => pure $ act env opts
    };
    (out, res) ← liftIO $ IO.Prim.withIsolatedStreams act;
    logInfo out;
    match res with
    | Except.error e => throw $ Exception.error $ ioErrorToMessage ctx ref e
    | Except.ok env  => do setEnv env; pure ()
  };
  let elabEval : CommandElabM Unit := do {
    -- fall back to non-meta eval if MetaHasEval hasn't been defined yet
    -- modify e to `HasEval.eval (hideUnit := false) e`
    act : IO Unit ← runTermElabM (some n) fun _ => do {
      e    ← Term.elabTerm term none;
      Term.synthesizeSyntheticMVars false;
      e ← Term.mkAppM `Lean.HasEval.eval #[e, toExpr false];
      addAndCompile e;
      env ← Term.getEnv;
      match env.evalConst (IO Unit) n with
      | Except.error e => Term.throwError e
      | Except.ok act  => pure act
    };
    (out, res) ← liftIO $ IO.Prim.withIsolatedStreams act;
    logInfo out;
    match res with
    | Except.error e => throw $ Exception.error $ ioErrorToMessage ctx ref e
    | Except.ok _    => pure ()
  };
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
    Term.synthesizeSyntheticMVars false;
    inst ← Term.instantiateMVars inst;
    val  ← Term.liftMetaM $ Meta.synthInstance inst;
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
  | _ => withRef val $ logError ("unexpected set_option value " ++ toString val)

/-
  `declId` is of the form
  ```
  parser! ident >> optional (".{" >> sepBy1 ident ", " >> "}")
  ```
  but we also accept a single identifier to users to make macro writing more convenient .
-/
def expandDeclId (declId : Syntax) : Name × Syntax :=
if declId.isIdent then
  (declId.getId, mkNullNode)
else
  let id             := declId.getIdAt 0;
  let optUnivDeclStx := declId.getArg 1;
  (id, optUnivDeclStx)

def withDeclId {α} (declId : Syntax) (f : Name → CommandElabM α) : CommandElabM α := do
-- ident >> optional (".{" >> sepBy1 ident ", " >> "}")
let (id, optUnivDeclStx) := expandDeclId declId;
savedLevelNames ← getLevelNames;
levelNames      ←
  if optUnivDeclStx.isNone then
    pure savedLevelNames
  else do {
    let extraLevels := (optUnivDeclStx.getArg 1).getArgs.getEvenElems;
    extraLevels.foldlM
      (fun levelNames idStx =>
        let id := idStx.getId;
        if levelNames.elem id then
          withRef idStx $ throwAlreadyDeclaredUniverseLevel id
        else
          pure (id :: levelNames))
      savedLevelNames
  };
withRef declId $
-- extract (optional) namespace part of id, after decoding macro scopes that would interfere with the check
let scpView := extractMacroScopes id;
match scpView.name with
| Name.str pre s _ =>
  /- Add back macro scopes. We assume a declaration like `def a.b[1,2] ...` with macro scopes `[1,2]`
     is always meant to mean `namespace a def b[1,2] ...`. -/
  let id := { scpView with name := mkNameSimple s }.review;
  withNamespace pre $ do
    modifyScope $ fun scope => { scope with levelNames := levelNames };
    finally (f id) (modifyScope $ fun scope => { scope with levelNames := savedLevelNames })
| _ => throwError "invalid declaration name"

/--
  Sort the given list of `usedParams` using the following order:
  - If it is an explicit level `allUserParams`, then use user given order.
  - Otherwise, use lexicographical.

  Remark: `scopeParams` are the universe params introduced using the `universe` command. `allUserParams` contains
  the universe params introduced using the `universe` command *and* the `.{...}` notation.

  Remark: this function return an exception if there is an `u` not in `usedParams`, that is in `allUserParams` but not in `scopeParams`.

  Remark: `explicitParams` are in reverse declaration order. That is, the head is the last declared parameter. -/
def sortDeclLevelParams (scopeParams : List Name) (allUserParams : List Name) (usedParams : Array Name) : Except String (List Name) :=
match allUserParams.find? $ fun u => !usedParams.contains u && !scopeParams.elem u with
| some u => throw ("unused universe parameter '" ++ toString u ++ "'")
| none   =>
  let result := allUserParams.foldl (fun result levelName => if usedParams.elem levelName then levelName :: result else result) [];
  let remaining := usedParams.filter (fun levelParam => !allUserParams.elem levelParam);
  let remaining := remaining.qsort Name.lt;
  pure $ result ++ remaining.toList

end Command
end Elab
end Lean
