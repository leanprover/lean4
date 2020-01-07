/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Elab.Alias
import Init.Lean.Elab.Log
import Init.Lean.Elab.ResolveName
import Init.Lean.Elab.Term
import Init.Lean.Elab.TermBinders

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
(nextMacroScope : Nat := 1)

instance State.inhabited : Inhabited State := ⟨{ env := arbitrary _ }⟩

def mkState (env : Environment) (messages : MessageLog := {}) (opts : Options := {}) : State :=
{ env := env, messages := messages, scopes := [{ kind := "root", header := "", opts := opts }] }

structure Context :=
(fileName       : String)
(fileMap        : FileMap)
(stateRef       : IO.Ref State)
(cmdPos         : String.Pos := 0)
(macroStack     : List Syntax := [])
(currMacroScope : MacroScope := 0)

abbrev CommandElabCoreM (ε) := ReaderT Context (EIO ε)
abbrev CommandElabM := CommandElabCoreM Exception
abbrev CommandElab  := SyntaxNode → CommandElabM Unit

def mkMessageAux (ctx : Context) (ref : Syntax) (msgData : MessageData) (severity : MessageSeverity) : Message :=
mkMessageCore ctx.fileName ctx.fileMap msgData severity (ref.getPos.getD ctx.cmdPos)

private def ioErrorToMessage (ctx : Context) (ref : Syntax) (err : IO.Error) : Message :=
mkMessageAux ctx ref (toString err) MessageSeverity.error

@[inline] def liftIOCore {α} (ctx : Context) (ref : Syntax) (x : IO α) : EIO Exception α :=
EIO.adaptExcept (ioErrorToMessage ctx ref) x

@[inline] def liftIO {α} (ref : Syntax) (x : IO α) : CommandElabM α :=
fun ctx => liftIOCore ctx ref x

private def getState : CommandElabM State :=
fun ctx => liftIOCore ctx Syntax.missing $ ctx.stateRef.get

private def setState (s : State) : CommandElabM Unit :=
fun ctx => liftIOCore ctx Syntax.missing $ ctx.stateRef.set s

@[inline] private def modifyGetState {α} (f : State → α × State) : CommandElabM α := do
s ← getState; let (a, s) := f s; setState s; pure a

instance CommandElabCoreM.monadState : MonadState State CommandElabM :=
{ get       := getState,
  set       := setState,
  modifyGet := @modifyGetState }

def getEnv : CommandElabM Environment := do s ← get; pure s.env
def getScope : CommandElabM Scope := do s ← get; pure s.scopes.head!
def getOptions : CommandElabM Options := do scope ← getScope; pure scope.opts

def addContext (msg : MessageData) : CommandElabM MessageData := do
env ← getEnv; opts ← getOptions;
pure (MessageData.withContext { env := env, mctx := {}, lctx := {}, opts := opts } msg)

instance CommandElabM.monadLog : MonadLog CommandElabM :=
{ getCmdPos   := do ctx ← read; pure ctx.cmdPos,
  getFileMap  := do ctx ← read; pure ctx.fileMap,
  getFileName := do ctx ← read; pure ctx.fileName,
  addContext  := addContext,
  logMessage  := fun msg => modify $ fun s => { messages := s.messages.add msg, .. s } }

/- If `ref` does not have position information, then try to use macroStack -/
private def getBetterRef (ref : Syntax) : CommandElabM Syntax :=
match ref.getPos with
| some _ => pure ref
| none   => do
  ctx ← read;
  match ctx.macroStack.find? $ fun (macro : Syntax) => macro.getPos != none with
  | some macro => pure macro
  | none       => pure ref

private def prettyPrint (stx : Syntax) : CommandElabM Format :=
match stx.reprint with -- TODO use syntax pretty printer
| some str => pure $ format str
| none     => pure $ format stx

private def addMacroStack (msgData : MessageData) : CommandElabM MessageData := do
ctx ← read;
if ctx.macroStack.isEmpty then pure msgData
else
  ctx.macroStack.foldlM
    (fun (msgData : MessageData) (macro : Syntax) => do
      macroFmt ← prettyPrint macro;
      pure (msgData ++ Format.line ++ "while expanding" ++ MessageData.nest 2 (Format.line ++ macroFmt)))
    msgData

/--
  Throws an error with the given `msgData` and extracting position information from `ref`.
  If `ref` does not contain position information, then use `cmdPos` -/
def throwError {α} (ref : Syntax) (msgData : MessageData) : CommandElabM α := do
ref ← getBetterRef ref;
msgData ← addMacroStack msgData;
msg ← mkMessage msgData MessageSeverity.error ref;
throw msg

def throwUnexpectedSyntax {α} (ref : Syntax) (expectedMsg : Option String := none) : CommandElabM α := do
refFmt ← prettyPrint ref;
match expectedMsg with
| none    => throwError ref ("unexpected syntax" ++ MessageData.nest 2 (Format.line ++ refFmt))
| some ex => throwError ref ("unexpected syntax, expected '" ++ ex ++ "'" ++ MessageData.nest 2 (Format.line ++ refFmt))

protected def getCurrMacroScope : CommandElabM Nat := do
ctx ← read;
pure ctx.currMacroScope

@[inline] protected def withFreshMacroScope {α} (x : CommandElabM α) : CommandElabM α := do
fresh ← modifyGet (fun st => (st.nextMacroScope, { st with nextMacroScope := st.nextMacroScope + 1 }));
adaptReader (fun (ctx : Context) => { ctx with currMacroScope := fresh }) x

instance CommandElabM.MonadQuotation : MonadQuotation CommandElabM := {
  getCurrMacroScope   := Command.getCurrMacroScope,
  withFreshMacroScope := @Command.withFreshMacroScope
}

abbrev CommandElabTable := ElabFnTable CommandElab
def mkBuiltinCommandElabTable : IO (IO.Ref CommandElabTable) := IO.mkRef {}
@[init mkBuiltinCommandElabTable] constant builtinCommandElabTable : IO.Ref CommandElabTable := arbitrary _

def addBuiltinCommandElab (k : SyntaxNodeKind) (declName : Name) (elab : CommandElab) : IO Unit := do
m ← builtinCommandElabTable.get;
when (m.contains k) $
  throw (IO.userError ("invalid builtin command elaborator, elaborator for '" ++ toString k ++ "' has already been defined"));
builtinCommandElabTable.modify $ fun m => m.insert k elab

def declareBuiltinCommandElab (env : Environment) (kind : SyntaxNodeKind) (declName : Name) : IO Environment :=
let name := `_regBuiltinCommandElab ++ declName;
let type := mkApp (mkConst `IO) (mkConst `Unit);
let val  := mkAppN (mkConst `Lean.Elab.Command.addBuiltinCommandElab) #[toExpr kind, toExpr declName, mkConst declName];
let decl := Declaration.defnDecl { name := name, lparams := [], type := type, value := val, hints := ReducibilityHints.opaque, isUnsafe := false };
match env.addAndCompile {} decl with
-- TODO: pretty print error
| Except.error _ => throw (IO.userError ("failed to emit registration code for builtin command elaborator '" ++ toString declName ++ "'"))
| Except.ok env  => IO.ofExcept (setInitAttr env name)

@[init] def registerBuiltinCommandElabAttr : IO Unit :=
registerAttribute {
 name  := `builtinCommandElab,
 descr := "Builtin command elaborator",
 add   := fun env declName arg persistent => do {
   unless persistent $ throw (IO.userError ("invalid attribute 'builtinCommandElab', must be persistent"));
   kind ← IO.ofExcept $ syntaxNodeKindOfAttrParam env `Lean.Parser.Command arg;
   match env.find? declName with
   | none  => throw "unknown declaration"
   | some decl =>
     match decl.type with
     | Expr.const `Lean.Elab.Command.CommandElab _ _ => declareBuiltinCommandElab env kind declName
     | _ => throw (IO.userError ("unexpected command elaborator type at '" ++ toString declName ++ "' `CommandElab` expected"))
 },
 applicationTime := AttributeApplicationTime.afterCompilation
}

abbrev CommandElabAttribute := ElabAttribute CommandElab
def mkCommandElabAttribute : IO CommandElabAttribute :=
mkElabAttribute CommandElab `commandElab `Lean.Parser.Command `Lean.Elab.Command.CommandElab "command" builtinCommandElabTable
@[init mkCommandElabAttribute] constant commandElabAttribute : CommandElabAttribute := arbitrary _

def elabCommand (stx : Syntax) : CommandElabM Unit :=
stx.ifNode
  (fun n => do
    s ← get;
    let table := (commandElabAttribute.ext.getState s.env).table;
    let k := n.getKind;
    match table.find? k with
    | some elab => elab n
    | none      => throwError stx ("command '" ++ toString k ++ "' has not been implemented"))
  (fun _ => throwError stx ("unexpected command"))

/- Elaborate `x` with `stx` on the macro stack -/
@[inline] def withMacroExpansion {α} (stx : Syntax) (x : CommandElabM α) : CommandElabM α :=
adaptReader (fun (ctx : Context) => { macroStack := stx :: ctx.macroStack, .. ctx }) x

/-- Adapt a syntax transformation to a regular, command-producing elaborator. -/
def adaptExpander (exp : Syntax → CommandElabM Syntax) : CommandElab :=
fun stx => withMacroExpansion stx.val $ do
  stx ← exp stx.val;
  elabCommand stx

private def mkTermContext (ctx : Context) (s : State) (declName? : Option Name) : Term.Context :=
let scope := s.scopes.head!;
{ config         := { opts := scope.opts, foApprox := true, ctxApprox := true, quasiPatternApprox := true, isDefEqStuckEx := true },
  fileName       := ctx.fileName,
  fileMap        := ctx.fileMap,
  cmdPos         := ctx.cmdPos,
  declName?      := declName?,
  macroStack     := ctx.macroStack,
  currMacroScope := ctx.currMacroScope,
  currNamespace  := scope.currNamespace,
  levelNames     := scope.levelNames,
  openDecls      := scope.openDecls }

private def mkTermState (s : State) : Term.State :=
{ env            := s.env,
  messages       := s.messages,
  nextMacroScope := s.nextMacroScope }

private def getVarDecls (s : State) : Array Syntax :=
s.scopes.head!.varDecls

private def toCommandResult {α} (ctx : Context) (s : State) (result : EStateM.Result Term.Exception Term.State α) : EStateM.Result Exception State α :=
match result with
| EStateM.Result.ok a newS                            => EStateM.Result.ok a { env := newS.env, messages := newS.messages, nextMacroScope := newS.nextMacroScope, .. s }
| EStateM.Result.error (Term.Exception.error ex) newS => EStateM.Result.error ex { env := newS.env, messages := newS.messages, nextMacroScope := newS.nextMacroScope, .. s }
| EStateM.Result.error Term.Exception.postpone newS   => unreachable!

instance CommandElabM.inhabited {α} : Inhabited (CommandElabM α) :=
⟨throw $ arbitrary _⟩

@[inline] def runTermElabM {α} (declName? : Option Name) (elab : Array Expr → TermElabM α) : CommandElabM α := do
ctx ← read;
s ← get;
match (Term.elabBinders (getVarDecls s) elab (mkTermContext ctx s declName?)).run (mkTermState s) with
| EStateM.Result.ok a newS                            => do modify $ fun s => { env := newS.env, messages := newS.messages, .. s }; pure a
| EStateM.Result.error (Term.Exception.error ex) newS => do modify $ fun s => { env := newS.env, messages := newS.messages, .. s }; throw ex
| EStateM.Result.error Term.Exception.postpone newS   => unreachable!

@[inline] def withLogging (x : CommandElabM Unit) : CommandElabM Unit :=
catch x (fun ex => do logMessage ex; pure ())

@[inline] def catchExceptions (x : CommandElabM Unit) : CommandElabCoreM Empty Unit :=
fun ctx => EIO.catchExceptions (withLogging x ctx) (fun _ => pure ())

def dbgTrace {α} [HasToString α] (a : α) : CommandElabM Unit :=
_root_.dbgTrace (toString a) $ fun _ => pure ()

def setEnv (newEnv : Environment) : CommandElabM Unit :=
modify $ fun s => { env := newEnv, .. s }

def getCurrNamespace : CommandElabM Name := do
scope ← getScope; pure scope.currNamespace

private def addScope (kind : String) (header : String) (newNamespace : Name) : CommandElabM Unit :=
modify $ fun s => {
  env    := s.env.registerNamespace newNamespace,
  scopes := { kind := kind, header := header, currNamespace := newNamespace, .. s.scopes.head! } :: s.scopes,
  .. s }

private def addScopes (ref : Syntax) (kind : String) (updateNamespace : Bool) : Name → CommandElabM Unit
| Name.anonymous => pure ()
| Name.str p header _ => do
  addScopes p;
  currNamespace ← getCurrNamespace;
  addScope kind header (if updateNamespace then currNamespace ++ header else currNamespace)
| _ => throwError ref "invalid scope"

private def addNamespace (ref : Syntax) (header : Name) : CommandElabM Unit :=
addScopes ref "namespace" true header

@[builtinCommandElab «namespace»] def elabNamespace : CommandElab :=
fun stx => match_syntax stx.val with
  | `(namespace $n) => addNamespace stx.val n.getId
  | _               => throwUnexpectedSyntax stx.val "namespace"

@[builtinCommandElab «section»] def elabSection : CommandElab :=
fun stx => match_syntax stx.val with
  | `(section $header:ident) => addScopes stx.val "section" false header.getId
  | `(section)               => do currNamespace ← getCurrNamespace; addScope "section" "" currNamespace
  | _                        => throwUnexpectedSyntax stx.val "section"

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
fun n => do
  let header? := (n.getArg 1).getOptionalIdent?;
  let endSize := match header? with
    | none   => 1
    | some n => n.getNumParts;
  scopes ← getScopes;
  if endSize < scopes.length then
    modify $ fun s => { scopes := s.scopes.drop endSize, .. s }
  else do {
    -- we keep "root" scope
    modify $ fun s => { scopes := s.scopes.drop (s.scopes.length - 1), .. s };
    throwError n.val "invalid 'end', insufficient scopes"
  };
  match header? with
  | none        => unless (checkAnonymousScope scopes) $ throwError n.val "invalid 'end', name is missing"
  | some header => unless (checkEndHeader header scopes) $ throwError n.val "invalid 'end', name mismatch"

@[inline] def withNamespace {α} (ref : Syntax) (ns : Name) (elab : CommandElabM α) : CommandElabM α := do
addNamespace ref ns;
a ← elab;
modify $ fun s => { scopes := s.scopes.drop ns.getNumParts, .. s };
pure a

@[specialize] def modifyScope (f : Scope → Scope) : CommandElabM Unit :=
modify $ fun s =>
  { scopes := match s.scopes with
    | h::t => f h :: t
    | []   => unreachable!,
    .. s }

def getLevelNames : CommandElabM (List Name) := do
scope ← getScope; pure scope.levelNames

def throwAlreadyDeclaredUniverseLevel {α} (ref : Syntax) (u : Name) : CommandElabM α :=
throwError ref ("a universe level named '" ++ toString u ++ "' has already been declared")

def addUnivLevel (idStx : Syntax) : CommandElabM Unit := do
let id := idStx.getId;
levelNames ← getLevelNames;
if levelNames.elem id then
  throwAlreadyDeclaredUniverseLevel idStx id
else
  modifyScope $ fun scope => { levelNames := id :: scope.levelNames, .. scope }

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
    throwError stx.val (ex.toMessageData opts)

def getOpenDecls : CommandElabM (List OpenDecl) := do
scope ← getScope; pure scope.openDecls

def logUnknownDecl (stx : Syntax) (declName : Name) : CommandElabM Unit :=
logError stx ("unknown declaration '" ++ toString declName ++ "'")

def resolveNamespace (id : Name) : CommandElabM Name := do
env           ← getEnv;
currNamespace ← getCurrNamespace;
openDecls ← getOpenDecls;
match Elab.resolveNamespace env currNamespace openDecls id with
| some ns => pure ns
| none    => throwErrorUsingCmdPos ("unknown namespace '" ++ toString id ++ "'")

@[builtinCommandElab «export»] def elabExport : CommandElab :=
fun stx => do
  -- `stx` is of the form (Command.export "export" <namespace> "(" (null <ids>*) ")")
  let id  := stx.getIdAt 1;
  ns ← resolveNamespace id;
  currNamespace ← getCurrNamespace;
  when (ns == currNamespace) $ throwError stx.val "invalid 'export', self export";
  env ← getEnv;
  let ids := (stx.getArg 3).getArgs;
  aliases ← ids.foldlM
   (fun (aliases : List (Name × Name)) (idStx : Syntax) => do {
      let id := idStx.getId;
      let declName := ns ++ id;
      if env.contains declName then
        pure $ (currNamespace ++ id, declName) :: aliases
      else do
        logUnknownDecl idStx declName;
        pure aliases
      })
    [];
  modify $ fun s => { env := aliases.foldl (fun env p => addAlias env p.1 p.2) s.env, .. s }

def addOpenDecl (d : OpenDecl) : CommandElabM Unit :=
modifyScope $ fun scope => { openDecls := d :: scope.openDecls, .. scope }

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
    logUnknownDecl idStx declName

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
    logUnknownDecl idStx declName;
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
    logUnknownDecl stx declName

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

/- We just ignore Lean3 notation declaration commands. -/
@[builtinCommandElab «mixfix»] def elabMixfix : CommandElab := fun _ => pure ()
@[builtinCommandElab «reserve»] def elabReserve : CommandElab := fun _ => pure ()
@[builtinCommandElab «notation»] def elabNotation : CommandElab := fun _ => pure ()

@[builtinCommandElab «variable»] def elabVariable : CommandElab :=
fun n => do
  -- `variable` bracktedBinder
  let binder := n.getArg 1;
  -- Try to elaborate `binder` for sanity checking
  runTermElabM none $ fun _ => Term.elabBinder binder $ fun _ => pure ();
  modifyScope $ fun scope => { varDecls := scope.varDecls.push binder, .. scope }

@[builtinCommandElab «variables»] def elabVariables : CommandElab :=
fun n => do
  -- `variables` bracktedBinder+
  let binders := (n.getArg 1).getArgs;
  -- Try to elaborate `binders` for sanity checking
  runTermElabM none $ fun _ => Term.elabBinders binders $ fun _ => pure ();
  modifyScope $ fun scope => { varDecls := scope.varDecls ++ binders, .. scope }

@[builtinCommandElab «check»] def elabCheck : CommandElab :=
fun stx => do
  let term := stx.getArg 1;
  runTermElabM none $ fun _ => do
    e    ← Term.elabTerm term none;
    Term.synthesizeSyntheticMVars false;
    type ← Term.inferType stx.val e;
    e    ← Term.instantiateMVars stx.val e;
    type ← Term.instantiateMVars stx.val type;
    logInfo stx.val (e ++ " : " ++ type);
    pure ()

@[inline] def withDeclId (declId : Syntax) (f : Name → CommandElabM Unit) : CommandElabM Unit := do
-- ident >> optional (".{" >> sepBy1 ident ", " >> "}")
let id             := declId.getIdAt 0;
let optUnivDeclStx := declId.getArg 1;
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
          throwAlreadyDeclaredUniverseLevel idStx id
        else
          pure (id :: levelNames))
      savedLevelNames
  };
let ref := declId;
match id with
| Name.str pre s _ => withNamespace ref pre $ do
  modifyScope $ fun scope => { levelNames := levelNames, .. scope };
  finally (f (mkNameSimple s)) (modifyScope $ fun scope => { levelNames := savedLevelNames, .. scope })
| _                => throwError ref "invalid declaration name"

/--
  Sort the given list of `usedParams` using the following order:
  - If it is an explicit level `explicitParams`, then use user given order.
  - Otherwise, use lexicographical.

  Remark: `explicitParams` are in reverse declaration order. That is, the head is the last declared parameter. -/
def sortDeclLevelParams (explicitParams : List Name) (usedParams : Array Name) : List Name :=
let result := explicitParams.foldl (fun result levelName => if usedParams.elem levelName then levelName :: result else result) [];
let remaining := usedParams.filter (fun levelParam => !explicitParams.elem levelParam);
let remaining := remaining.qsort Name.lt;
result ++ remaining.toList

def addDecl (ref : Syntax) (decl : Declaration) : CommandElabM Unit := do
env ← getEnv;
match env.addDecl decl with
| Except.ok    env => modify $ fun s => { env := env, .. s }
| Except.error kex => do
  opts ← getOptions;
  throwError ref (kex.toMessageData opts)

end Command
end Elab
end Lean
