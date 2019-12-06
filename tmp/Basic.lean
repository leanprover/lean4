/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Control.Reader
import Init.Lean.Meta
import Init.Lean.Parser.Module

namespace Lean
namespace Elab

/-
structure ElabContext :=
(fileName : String)
(fileMap  : FileMap)

structure ElabScope :=
(cmd         : String)
(header      : Name)
(options     : Options := {})
(ns          : Name := Name.anonymous) -- current namespace
(openDecls   : List OpenDecl := [])
(univs       : List Name := [])
(lctx        : LocalContext := {})
(nextInstIdx : Nat := 1)
(inPattern   : Bool := false)

namespace ElabScope

instance : Inhabited ElabScope := ⟨{ cmd := "", header := arbitrary _ }⟩

end ElabScope

structure ElabState :=
(env      : Environment)
(messages : MessageLog := {})
(cmdPos   : String.Pos := 0)
(ngen     : NameGenerator := {})
(mctx     : MetavarContext := {})
(scopes   : List ElabScope := [{ cmd := "root", header := Name.anonymous }])

inductive ElabException
| io     : IO.Error → ElabException
| msg    : Message → ElabException
| kernel : KernelException → ElabException
| other  : String → ElabException
/- ElabException.silent is used when we log an error in `messages`, and then
   want to interrupt the elaborator execution. We use it to make sure the
   top-level handler does not record it again in `messages`. See `logErrorAndThrow` -/
| silent : ElabException

namespace ElabException

instance : Inhabited ElabException := ⟨other "error"⟩

end ElabException

abbrev Elab := ReaderT ElabContext (EStateM ElabException ElabState)

instance str2ElabException : HasCoe String ElabException := ⟨ElabException.other⟩

abbrev TermElab    := SyntaxNode Expr → Option Expr → Elab (Syntax Expr)
abbrev CommandElab := SyntaxNode → Elab Unit

abbrev TermElabTable : Type := SMap SyntaxNodeKind TermElab
abbrev CommandElabTable : Type := SMap SyntaxNodeKind CommandElab
def mkBuiltinTermElabTable : IO (IO.Ref TermElabTable) :=  IO.mkRef {}
def mkBuiltinCommandElabTable : IO (IO.Ref CommandElabTable) := IO.mkRef {}
@[init mkBuiltinTermElabTable]
constant builtinTermElabTable : IO.Ref TermElabTable := arbitrary _
@[init mkBuiltinCommandElabTable]
constant builtinCommandElabTable : IO.Ref CommandElabTable := arbitrary _

def addBuiltinTermElab (k : SyntaxNodeKind) (declName : Name) (elab : TermElab) : IO Unit :=
do m ← builtinTermElabTable.get;
   when (m.contains k) $
     throw (IO.userError ("invalid builtin term elaborator, elaborator for '" ++ toString k ++ "' has already been defined"));
   builtinTermElabTable.modify $ fun m => m.insert k elab

def addBuiltinCommandElab (k : SyntaxNodeKind) (declName : Name) (elab : CommandElab) : IO Unit :=
do m ← builtinCommandElabTable.get;
   when (m.contains k) $
     throw (IO.userError ("invalid builtin command elaborator, elaborator for '" ++ toString k ++ "' has already been defined"));
   builtinCommandElabTable.modify $ fun m => m.insert k elab

def checkSyntaxNodeKind (k : Name) : IO Name :=
do b ← Parser.isValidSyntaxNodeKind k;
  if b then pure k
  else throw (IO.userError "failed")

def checkSyntaxNodeKindAtNamespaces (k : Name) : List Name → IO Name
| []    => throw (IO.userError "failed")
| n::ns => checkSyntaxNodeKind (n ++ k) <|> checkSyntaxNodeKindAtNamespaces ns

def syntaxNodeKindOfAttrParam (env : Environment) (parserNamespace : Name) (arg : Syntax) : IO SyntaxNodeKind :=
match attrParamSyntaxToIdentifier arg with
| some k =>
  checkSyntaxNodeKind k
  <|>
  checkSyntaxNodeKindAtNamespaces k env.getNamespaces
  <|>
  checkSyntaxNodeKind (parserNamespace ++ k)
  <|>
  throw (IO.userError ("invalid syntax node kind '" ++ toString k ++ "'"))
| none   => throw (IO.userError ("syntax node kind is missing"))

def declareBuiltinElab (env : Environment) (addFn : Name) (kind : SyntaxNodeKind) (declName : Name) : IO Environment :=
let name := `_regBuiltinTermElab ++ declName;
let type := mkApp (mkConst `IO) (mkConst `Unit);
let val  := mkAppN (mkConst addFn) #[toExpr kind, toExpr declName, mkConst declName];
let decl := Declaration.defnDecl { name := name, lparams := [], type := type, value := val, hints := ReducibilityHints.opaque, isUnsafe := false };
match env.addAndCompile {} decl with
-- TODO: pretty print error
| Except.error _ => throw (IO.userError ("failed to emit registration code for builtin term elaborator '" ++ toString declName ++ "'"))
| Except.ok env  => IO.ofExcept (setInitAttr env name)

def declareBuiltinTermElab (env : Environment) (kind : SyntaxNodeKind) (declName : Name) : IO Environment :=
declareBuiltinElab env `Lean.addBuiltinTermElab kind declName

def declareBuiltinCommandElab (env : Environment) (kind : SyntaxNodeKind) (declName : Name) : IO Environment :=
declareBuiltinElab env `Lean.addBuiltinCommandElab kind declName

@[init] def registerBuiltinTermElabAttr : IO Unit :=
registerAttribute {
 name  := `builtinTermElab,
 descr := "Builtin term elaborator",
 add   := fun env declName arg persistent => do {
   unless persistent $ throw (IO.userError ("invalid attribute 'builtinTermElab', must be persistent"));
   kind ← syntaxNodeKindOfAttrParam env `Lean.Parser.Term arg;
   match env.find declName with
   | none  => throw "unknown declaration"
   | some decl =>
     match decl.type with
     | Expr.const `Lean.TermElab _ _ => declareBuiltinTermElab env kind declName
     | _ => throw (IO.userError ("unexpected term elaborator type at '" ++ toString declName ++ "' `TermElab` expected"))
 },
 applicationTime := AttributeApplicationTime.afterCompilation
}

@[init] def registerBuiltinCommandElabAttr : IO Unit :=
registerAttribute {
 name  := `builtinCommandElab,
 descr := "Builtin command elaborator",
 add   := fun env declName arg persistent => do {
   unless persistent $ throw (IO.userError ("invalid attribute 'builtinCommandElab', must be persistent"));
   kind ← syntaxNodeKindOfAttrParam env `Lean.Parser.Command arg;
   match env.find declName with
   | none  => throw "unknown declaration"
   | some decl =>
     match decl.type with
     | Expr.const `Lean.CommandElab _ _ => declareBuiltinCommandElab env kind declName
     | _ => throw (IO.userError ("unexpected command elaborator type at '" ++ toString declName ++ "' `CommandElab` expected"))
 },
 applicationTime := AttributeApplicationTime.afterCompilation
}

structure ElabAttributeEntry :=
(kind     : SyntaxNodeKind)
(declName : Name)

structure ElabAttribute (σ : Type) :=
(attr : AttributeImpl)
(ext  : PersistentEnvExtension ElabAttributeEntry σ)
(kind : String)

namespace ElabAttribute

instance {σ} [Inhabited σ] : Inhabited (ElabAttribute σ) := ⟨{ attr := arbitrary _, ext := arbitrary _, kind := "" }⟩

end ElabAttribute

/-
This is just the basic skeleton for the `[termElab]` attribute and environment extension.
The state is initialized using `builtinTermElabTable`.

The current implementation just uses the bultin elaborators.
-/
def mkElabAttribute {σ} [Inhabited σ] (attrName : Name) (kind : String) (builtinTable : IO.Ref σ) : IO (ElabAttribute σ) :=
do ext : PersistentEnvExtension ElabAttributeEntry σ ← registerPersistentEnvExtension {
     name            := attrName,
     addImportedFn   := fun es => do
       table ← builtinTable.get;
       -- TODO: populate table with `es`
       pure table,
     addEntryFn      := fun (s : σ) _ => s,                            -- TODO
     exportEntriesFn := fun _ => #[],                                  -- TODO
     statsFn         := fun _ => fmt (kind ++ " elaborator attribute") -- TODO
   };
   let attrImpl : AttributeImpl := {
     name  := attrName,
     descr := kind ++ " elaborator",
     add   := fun env decl args persistent => pure env -- TODO
   };
   pure { ext := ext, attr := attrImpl, kind := kind }

abbrev TermElabAttribute := ElabAttribute TermElabTable
def mkTermElabAttribute : IO TermElabAttribute :=
mkElabAttribute `elabTerm "term" builtinTermElabTable
@[init mkTermElabAttribute]
constant termElabAttribute : TermElabAttribute := arbitrary _

abbrev CommandElabAttribute := ElabAttribute CommandElabTable
def mkCommandElabAttribute : IO CommandElabAttribute :=
mkElabAttribute `commandTerm "command" builtinCommandElabTable
@[init mkCommandElabAttribute]
constant commandElabAttribute : CommandElabAttribute := arbitrary _

namespace Elab
def logMessage (msg : Message) : Elab Unit :=
modify $ fun s => { messages := s.messages.add msg, .. s }

def getPosition (pos : Option String.Pos := none) : Elab Position :=
do ctx ← read;
   s ← get;
   pure $ ctx.fileMap.toPosition (pos.getD s.cmdPos)

def mkMessage (msg : String) (pos : Option String.Pos := none) : Elab Message :=
do ctx ← read;
   s ← get;
   let pos := ctx.fileMap.toPosition (pos.getD s.cmdPos);
   pure { fileName := ctx.fileName, pos := pos, data := msg }

def logErrorAt (pos : String.Pos) (errorMsg : String) : Elab Unit :=
mkMessage errorMsg pos >>= logMessage

def logErrorUsingCmdPos (errorMsg : String) : Elab Unit :=
do s ← get;
   logErrorAt s.cmdPos errorMsg

def getPos {α} (stx : Syntax α) : Elab String.Pos :=
match stx.getPos with
| some p => pure p
| none   => do s ← get; pure s.cmdPos

def logError {α} (stx : Syntax α) (errorMsg : String) : Elab Unit :=
do pos ← getPos stx;
   logErrorAt pos errorMsg

def logElabException (e : ElabException) : Elab Unit :=
let log (msg : Message) : Elab Unit :=
  modify $ fun s => { messages := s.messages.add msg, .. s };
match e with
| ElabException.silent   => pure () -- do nothing since message was already logged
| ElabException.msg m    => log m
| ElabException.io e     => mkMessage (toString e) >>= log
| ElabException.other e  => mkMessage e >>= log
| ElabException.kernel e =>
  match e with
  | KernelException.other msg => mkMessage msg >>= log
  | _                         => mkMessage "kernel exception" >>= log -- TODO(pretty print them)

def logErrorAndThrow {α β : Type} (stx : Syntax β) (errorMsg : String) : Elab α :=
do logError stx errorMsg;
   throw ElabException.silent

def logUnknownDecl {α} (stx : Syntax α) (declName : Name) : Elab Unit :=
logError stx ("unknown declaration '" ++ toString declName ++ "'")

def getEnv : Elab Environment :=
do s ← get; pure s.env

def setEnv (env : Environment) : Elab Unit :=
modify $ fun s => { env := env, .. s }

def elabCommand (stx : Syntax) : Elab Unit :=
stx.ifNode
  (fun n => do
    s ← get;
    let tables := commandElabAttribute.ext.getState s.env;
    let k := n.getKind;
    match tables.find k with
    | some elab => elab n
    | none      => logError stx ("command '" ++ toString k ++ "' has not been implemented"))
  (fun _ => logErrorUsingCmdPos ("unexpected command"))
-/

structure ElabContext :=
(fileName : String)
(fileMap  : FileMap)

inductive ElabException
| io     : IO.Error → ElabException
| msg    : Message → ElabException
| kernel : KernelException → ElabException

structure ElabState :=
(dummy : Unit := ())

structure FrontendState :=
(elabState   : ElabState)
(parserState : Parser.ModuleParserState)

abbrev Frontend := ReaderT Parser.ParserContextCore (EStateM ElabException FrontendState)

/-
def getElabContext : Frontend ElabContext :=
do c ← read;
   pure { fileName := c.fileName, fileMap := c.fileMap }

@[specialize] def runElab {α} (x : Elab α) : Frontend α :=
do c ← getElabContext;
   monadLift $ EStateM.adaptState
      (fun (s : FrontendState) => (s.elabState, s.parserState))
      (fun es ps => { elabState := es, parserState := ps })
      (x c)

def elabCommandAtFrontend (stx : Syntax) : Frontend Unit :=
runElab (elabCommand stx)

def updateCmdPos : Frontend Unit :=
modify $ fun s => { elabState := { cmdPos := s.parserState.pos, .. s.elabState }, .. s }

def processCommand : Frontend Bool :=
do updateCmdPos;
   s ← get;
   let es := s.elabState;
   let ps := s.parserState;
   c ← read;
   match Parser.parseCommand es.env c ps es.messages with
   | (cmd, ps, messages) => do
     set { elabState := { messages := messages, .. es }, parserState := ps };
     if Parser.isEOI cmd || Parser.isExitCommand cmd then do
       pure true -- Done
     else do
       catch (elabCommandAtFrontend cmd) $ fun e => runElab (logElabException e);
       pure false

partial def processCommandsAux : Unit → Frontend Unit
| () => do
  done ← processCommand;
  if done then pure ()
  else processCommandsAux ()

def processCommands : Frontend Unit :=
processCommandsAux ()

def testFrontend (input : String) (fileName : Option String := none) : IO (Environment × MessageLog) :=
do env ← mkEmptyEnvironment;
   let fileName := fileName.getD "<input>";
   let ctx := Parser.mkParserContextCore env input fileName;
   match Parser.parseHeader env ctx with
   | (header, parserState, messages) => do
     (env, messages) ← processHeader header messages ctx;
     let elabState := { ElabState . env := env, messages := messages };
     match (processCommands ctx).run { elabState := elabState, parserState := parserState } with
       | EStateM.Result.ok _ s    => pure (s.elabState.env, s.elabState.messages)
       | EStateM.Result.error _ s => pure (s.elabState.env, s.elabState.messages)

instance {α} : Inhabited (Elab α) :=
⟨fun _ => arbitrary _⟩

def mkFreshName : Elab Name :=
modifyGet $ fun s => (s.ngen.curr, { ngen := s.ngen.next, .. s })

def getScope : Elab ElabScope :=
do s ← get; pure s.scopes.head!

def getOpenDecls : Elab (List OpenDecl) :=
ElabScope.openDecls <$> getScope

def getUniverses : Elab (List Name) :=
ElabScope.univs <$> getScope

def getNamespace : Elab Name :=
do s ← get;
   match s.scopes with
   | []      => pure Name.anonymous
   | (sc::_) => pure sc.ns

@[specialize] def modifyScope (f : ElabScope → ElabScope) : Elab Unit :=
modify $ fun s =>
  { scopes := match s.scopes with
    | h::t => f h :: t
    | []   => [], -- unreachable
    .. s }

@[specialize] def modifyGetScope {α} [Inhabited α] (f : ElabScope → α × ElabScope) : Elab α :=
modifyGet $ fun s =>
  match s with
  | { scopes := h::t, .. } =>
    let (a, h) := f h;
    (a, { scopes := h :: t, .. s })
  | _ => (arbitrary _, s)

def localContext : Elab LocalContext :=
do scope ← getScope; pure scope.lctx

def mkLocalDecl (userName : Name) (type : Expr) (bi : BinderInfo := BinderInfo.default) : Elab Expr :=
do idx ← mkFreshName;
   modifyScope $ fun scope => { lctx := scope.lctx.mkLocalDecl idx userName type bi, .. scope };
   pure (mkFVar idx)

def mkLambda (xs : Array Expr) (b : Expr) : Elab Expr :=
do lctx ← localContext; pure $ lctx.mkLambda xs b

def mkForall (xs : Array Expr) (b : Expr) : Elab Expr :=
do lctx ← localContext; pure $ lctx.mkForall xs b

def anonymousInstNamePrefix := `_inst

def mkAnonymousInstName : Elab Name :=
do scope ← getScope;
   let n := anonymousInstNamePrefix.appendIndexAfter scope.nextInstIdx;
   modifyScope $ fun scope => { nextInstIdx := scope.nextInstIdx + 1, .. scope };
   pure n

def resolveNamespaceUsingScopes (env : Environment) (n : Name) : List ElabScope → Option Name
| [] => none
| { ns := ns, .. } :: scopes   => if isNamespace env (ns ++ n) then some (ns ++ n) else resolveNamespaceUsingScopes scopes

def resolveNamespaceUsingOpenDecls (env : Environment) (n : Name) : List OpenDecl → Option Name
| []                          => none
| OpenDecl.simple ns [] :: ds =>  if isNamespace env (ns ++ n) then some (ns ++ n) else resolveNamespaceUsingOpenDecls ds
| _ :: ds                     => resolveNamespaceUsingOpenDecls ds

/-
Given a name `n` try to find namespace it refers to. The resolution procedure works as follows
1- If `n` is the extact name of an existing namespace, then return `n`
2- If `n` is in the scope of `namespace` commands declaring namespace headers `h_1`, ..., `h_n`,
   then return `h_1 ++ ... ++ h_i ++ n` if it is the name of an existing namespace. We search "backwards".
3- Finally, for each command `open N`, return `N ++ n` if it is the name of an existing namespace.
   We search "backwards" again. That is, we try the most recent `open` command first.
   We only consider simple `open` commands.
-/
def resolveNamespace (n : Name) : Elab Name :=
do s ← get;
   if isNamespace s.env n then pure n
   else match resolveNamespaceUsingScopes s.env n s.scopes  with
     | some n => pure n
     | none   => do
       openDecls ← getOpenDecls;
       match resolveNamespaceUsingOpenDecls s.env n openDecls with
       | some n => pure n
       | none   => throw (ElabException.other ("unknown namespace '" ++ toString n ++ "'"))

@[inline] def withNewScope {α} (x : Elab α) : Elab α :=
do modify $ fun s => { scopes := s.scopes.head! :: s.scopes, .. s };
   a ← x;
   modify $ fun s => { scopes := s.scopes.tail!, .. s};
   pure a

@[inline] def withInPattern {α} (x : Elab α) : Elab α :=
withNewScope $ do
  modifyScope $ fun scope => { inPattern := true, .. scope };
  x

def inPattern : Elab Bool :=
do scope ← getScope; pure $ scope.inPattern

/- Remark: in an ideal world where performance doesn't matter, we would define `Elab` as
   ```
   ExceptT ElabException (StateT ElabException IO)
   ```
   and we would not need unsafe features for implementing `runIO`.
   We say `Elab` is "morally" built on top of `IO`. -/
unsafe def runIOUnsafe {α : Type} (x : IO α) : Elab α :=
match unsafeIO x with
| Except.ok a    => pure a
| Except.error e => throw (ElabException.io e)

@[implementedBy runIOUnsafe]
constant runIO {α : Type} (x : IO α) : Elab α := arbitrary _

end Elab
-/
end Elab
end Lean
