/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.control.reader
import init.lean.namegenerator
import init.lean.scopes
import init.lean.parser.module

namespace Lean

inductive OpenDecl
| simple (ns : Name)
| explicit (ns : Name) (ids : List Name)
| «hiding» (ns : Name) (ex : List Name)
| «renaming» (ns : Name) (renames : List (Name × Name))

structure ElabContext :=
(fileName : String)
(fileMap  : FileMap)

structure ElabScope :=
(cmd       : String)
(header    : Name)
(options   : Options := {})
(ns        : Name := Name.anonymous) -- current namespace
(openDecls : List OpenDecl := [])

namespace ElabScope

instance : Inhabited ElabScope := ⟨{ cmd := "", header := default _ }⟩

end ElabScope

structure ElabState :=
(env      : Environment)
(messages : MessageLog := {})
(cmdPos   : String.Pos := 0)
(ngen     : NameGenerator := {})
(scopes   : List ElabScope := [{ cmd := "root", header := Name.anonymous }])

inductive ElabException
| io    : IO.Error → ElabException
| msg   : Message → ElabException
| other : String → ElabException

namespace ElabException

instance : Inhabited ElabException := ⟨other "error"⟩

end ElabException

abbrev Elab := ReaderT ElabContext (EState ElabException ElabState)

instance str2ElabException : HasCoe String ElabException := ⟨ElabException.other⟩

abbrev TermElab    := SyntaxNode → Elab Expr
abbrev CommandElab := SyntaxNode → Elab Unit

abbrev TermElabTable : Type := SMap SyntaxNodeKind TermElab Name.quickLt
abbrev CommandElabTable : Type := SMap SyntaxNodeKind CommandElab Name.quickLt
def mkBuiltinTermElabTable : IO (IO.Ref TermElabTable) :=  IO.mkRef {}
def mkBuiltinCommandElabTable : IO (IO.Ref CommandElabTable) := IO.mkRef {}
@[init mkBuiltinTermElabTable]
constant builtinTermElabTable : IO.Ref TermElabTable := default _
@[init mkBuiltinCommandElabTable]
constant builtinCommandElabTable : IO.Ref CommandElabTable := default _

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
| []      := throw (IO.userError "failed")
| (n::ns) := checkSyntaxNodeKind (n ++ k) <|> checkSyntaxNodeKindAtNamespaces ns

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
let type := Expr.app (mkConst `IO) (mkConst `Unit);
let val  := mkCApp addFn [toExpr kind, toExpr declName, mkConst declName];
let decl := Declaration.defnDecl { name := name, lparams := [], type := type, value := val, hints := ReducibilityHints.opaque, isUnsafe := false };
match env.addAndCompile {} decl with
| none     => throw (IO.userError ("failed to emit registration code for builtin term elaborator '" ++ toString declName ++ "'"))
| some env => IO.ofExcept (setInitAttr env name)

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
     | Expr.const `Lean.TermElab _ => declareBuiltinTermElab env kind declName
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
     | Expr.const `Lean.CommandElab _ => declareBuiltinCommandElab env kind declName
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

instance {σ} [Inhabited σ] : Inhabited (ElabAttribute σ) := ⟨{ attr := default _, ext := default _, kind := "" }⟩

end ElabAttribute

/-
This is just the basic skeleton for the `[termElab]` attribute and environment extension.
The state is initialized using `builtinTermElabTable`.

The current implementation just uses the bultin elaborators.
-/
def mkElabAttribute {σ} [Inhabited σ] (attrName : Name) (kind : String) (builtinTable : IO.Ref σ) : IO (ElabAttribute σ) :=
do
ext : PersistentEnvExtension ElabAttributeEntry σ ← registerPersistentEnvExtension {
  name            := attrName,
  addImportedFn   := fun es => do
    table ← builtinTable.get;
    -- TODO: populate table with `es`
    pure table,
  addEntryFn      := fun (s : σ) _ => s,                            -- TODO
  exportEntriesFn := fun _ => Array.empty,                          -- TODO
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
constant termElabAttribute : TermElabAttribute := default _

abbrev CommandElabAttribute := ElabAttribute CommandElabTable
def mkCommandElabAttribute : IO CommandElabAttribute :=
mkElabAttribute `commandTerm "command" builtinCommandElabTable
@[init mkCommandElabAttribute]
constant commandElabAttribute : CommandElabAttribute := default _

def mkMessage (msg : String) (pos : Option String.Pos := none) : Elab Message :=
do ctx ← read;
   s ← get;
   let pos := ctx.fileMap.toPosition (pos.getOrElse s.cmdPos);
   pure { filename := ctx.fileName, pos := pos, text := msg }

def logErrorAt (pos : String.Pos) (errorMsg : String) : Elab Unit :=
do msg ← mkMessage errorMsg pos;
   modify (fun s => { messages := s.messages.add msg, .. s })

def logErrorUsingCmdPos (errorMsg : String) : Elab Unit :=
do s ← get;
   logErrorAt s.cmdPos errorMsg

def getPos (stx : Syntax) : Elab String.Pos :=
match stx.getPos with
| some p => pure p
| none   => do s ← get; pure s.cmdPos

def logError (stx : Syntax) (errorMsg : String) : Elab Unit :=
do pos ← getPos stx;
   logErrorAt pos errorMsg

def toMessage : ElabException → Elab Message
| (ElabException.msg m)   := pure m
| (ElabException.io e)    := mkMessage (toString e)
| (ElabException.other e) := mkMessage e

def logElabException (e : ElabException) : Elab Unit :=
do msg ← toMessage e;
   modify (fun s => { messages := s.messages.add msg, .. s })

def logErrorAndThrow {α : Type} (stx : Syntax) (errorMsg : String) : Elab α :=
do logError stx errorMsg;
   throw errorMsg

def elabTerm (stx : Syntax) : Elab Expr :=
stx.ifNode
  (fun n => do
    s ← get;
    let tables := termElabAttribute.ext.getState s.env;
    let k      := n.getKind;
    match tables.find k with
    | some elab => elab n
    | none      => logErrorAndThrow stx ("term elaborator failed, no support for syntax '" ++ toString k ++ "'"))
  (fun _ => throw "term elaborator failed, unexpected syntax")

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

structure FrontendState :=
(elabState   : ElabState)
(parserState : Parser.ModuleParserState)

abbrev Frontend := ReaderT Parser.ParserContextCore (EState ElabException FrontendState)

def getElabContext : Frontend ElabContext :=
do c ← read;
   pure { fileName := c.filename, fileMap := c.fileMap }

@[specialize] def runElab {α} (x : Elab α) : Frontend α :=
do c ← getElabContext;
   monadLift $ EState.adaptState (x c)
      (fun (s : FrontendState) => (s.elabState, s.parserState))
      (fun es ps => { elabState := es, parserState := ps })

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
| () := do
  done ← processCommand;
  if done then pure ()
  else processCommandsAux ()

def processCommands : Frontend Unit :=
processCommandsAux ()

def absolutizeModuleName (m : Name) (k : Option Nat) : IO Name :=
do unless (k == none) $ throw ("relative imports are not supported yet"); -- TODO
   -- TODO: check whether the .olean file exists and use `m.default` when it doesn't.
   pure m

def processHeaderAux (header : Syntax) (trustLevel : UInt32) : IO Environment :=
do let header     := header.asNode;
   let imports    := if (header.getArg 0).isNone then [`init.default] else [];
   let modImports := (header.getArg 1).getArgs;
   imports ← modImports.mfoldl (fun imports stx =>
     -- `stx` is of the form `(Module.import "import" (null ...))
     let importPaths := (stx.getArg 1).getArgs; -- .asNode.getArgs;
     importPaths.mfoldl (fun imports stx => do
       -- `stx` is of the form `(Module.importPath (null "*"*) <id>)
       let stx := stx.asNode;
       let rel := stx.getArg 0;
       let k   := if rel.isNone then none else some (rel.getNumArgs);
       let id  := (stx.getArg 1).getIdentVal;
       m ← absolutizeModuleName id k;
       pure (m::imports))
       imports)
     imports;
   let imports := imports.reverse;
   importModules imports trustLevel

def processHeader (header : Syntax) (messages : MessageLog) (ctx : Parser.ParserContextCore) (trustLevel : UInt32 := 0) : IO (Environment × MessageLog) :=
catch
  (do env ← processHeaderAux header trustLevel;
      pure (env, messages))
  (fun e => do
     env ← mkEmptyEnvironment;
     let spos := header.getPos.getOrElse 0;
     let pos  := ctx.fileMap.toPosition spos;
     pure (env, messages.add { filename := ctx.filename, text := toString e, pos := pos }))

/- TODO: support for non-standard search path for web interface -/
@[extern 1 "lean_set_search_path"]
constant setSearchPathOld : IO Unit := default _

def testFrontend (input : String) (fileName : Option String := none) : IO (Environment × MessageLog) :=
do setSearchPathOld;
   env ← mkEmptyEnvironment;
   let fileName := fileName.getOrElse "<input>";
   let ctx := Parser.mkParserContextCore env input fileName;
   match Parser.parseHeader env ctx with
   | (header, parserState, messages) => do
     (env, messages) ← processHeader header messages ctx;
     let elabState := { ElabState . env := env, messages := messages };
     match (processCommands ctx).run { elabState := elabState, parserState := parserState } with
       | EState.Result.ok _ s    => pure (s.elabState.env, s.elabState.messages)
       | EState.Result.error _ s => pure (s.elabState.env, s.elabState.messages)

namespace Elab

instance {α} : Inhabited (Elab α) :=
⟨fun _ => default _⟩

def getOpenDecls : Elab (List OpenDecl) :=
do s ← get;
   pure s.scopes.head.openDecls

def getNamespace : Elab Name :=
do s ← get;
   match s.scopes with
   | []      => pure Name.anonymous
   | (sc::_) => pure sc.ns

def rootNamespace := `_root_

def removeRoot (n : Name) : Name :=
n.replacePrefix rootNamespace Name.anonymous

def resolveNamespaceUsingScopes (env : Environment) (n : Name) : List ElabScope → Option Name
| [] := none
| ({ ns := ns, .. } :: scopes) := if isNamespace env (ns ++ n) then some (ns ++ n) else resolveNamespaceUsingScopes scopes

def resolveNamespaceUsingOpenDecls (env : Environment) (n : Name) : List OpenDecl → Option Name
| []                         := none
| (OpenDecl.simple ns :: ds) :=  if isNamespace env (ns ++ n) then some (ns ++ n) else resolveNamespaceUsingOpenDecls ds
| (_ :: ds)                  := resolveNamespaceUsingOpenDecls ds

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
constant runIO {α : Type} (x : IO α) : Elab α := default _

end Elab

end Lean
