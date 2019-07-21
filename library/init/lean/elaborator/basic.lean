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

structure ElabContext :=
(fileName : String)
(fileMap  : FileMap)

structure ElabScope :=
(cmd     : String)
(header  : Name)
(options : Options := {})

structure ElabState :=
(env      : Environment)
(messages : MessageLog := {})
(cmdPos   : String.Pos := 0)
(ngen     : NameGenerator := {})
(scopes   : List ElabScope := [])

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

def logErrorAt (pos : String.Pos) (errorMsg : String) : Elab Unit :=
do ctx ← read;
   let pos := ctx.fileMap.toPosition pos;
   let msg := { Message . filename := ctx.fileName, pos := pos, text := errorMsg };
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
    | none      => logError stx ("command elaborator failed, no support for syntax '" ++ toString k ++ "'"))
  (fun _ => logErrorUsingCmdPos ("command elaborator failed, unexpected syntax"))

structure FrontendState :=
(elabState   : ElabState)
(parserState : Parser.ModuleParserState)

abbrev Frontend := ReaderT Parser.ParserContextCore (EState ElabException FrontendState)

def getElabContext : Frontend ElabContext :=
do c ← read;
   pure { fileName := c.filename, fileMap := c.fileMap }

def elabCommandAtFrontend (stx : Syntax) : Frontend Unit :=
do c ← getElabContext;
   monadLift $ EState.adaptState (elabCommand stx c)
      (fun (s : FrontendState) => (s.elabState, s.parserState))
      (fun es ps => { elabState := es, parserState := ps })

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
       elabCommandAtFrontend cmd;
       pure false

partial def processCommandsAux : Unit → Frontend Unit
| () := do
  done ← processCommand;
  if done then pure ()
  else processCommandsAux ()

def processCommands : Frontend Unit :=
processCommandsAux ()

def processHeader (header : Syntax) (messages : MessageLog) : IO (Environment × MessageLog) :=
do IO.println header;
   -- TODO
   env ← mkEmptyEnvironment;
   pure (env, messages)

def testFrontend (input : String) (fileName := "<input>") : IO (Environment × MessageLog) :=
do env ← mkEmptyEnvironment;
   let ctx := Parser.mkParserContextCore env input fileName;
   match Parser.parseHeader env ctx with
   | (header, parserState, messages) => do
     (env, messages) ← processHeader header messages;
     let elabState := { ElabState . env := env, messages := messages };
     match (processCommands ctx).run { elabState := elabState, parserState := parserState } with
       | EState.Result.ok _ s    => pure (s.elabState.env, s.elabState.messages)
       | EState.Result.error _ s => pure (s.elabState.env, s.elabState.messages)


namespace Elab

instance {α} : Inhabited (Elab α) :=
⟨fun _ => default _⟩

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
