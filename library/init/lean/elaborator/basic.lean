/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.lean.namegenerator
import init.lean.scopes
import init.lean.parser.module

namespace Lean

structure ElabScope :=
(options : Options := {})

structure ElabState :=
(env      : Environment)
(parser   : Parser.ModuleParser)
(ngen     : NameGenerator := {})
(scopes   : List ElabScope := [])

inductive ElabException
| io    : IO.Error → ElabException
| msg   : Message → ElabException
| other : String → ElabException

namespace ElabException

instance : Inhabited ElabException := ⟨other "error"⟩

end ElabException

abbrev Elab := EState ElabException ElabState

abbrev TermElab    := Syntax → Elab Expr
abbrev CommandElab := Syntax → Elab Unit

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
do s ← get;
   let ctx := s.parser.context;
   let pos := ctx.fileMap.toPosition pos;
   let msg := { Message . filename := ctx.filename, pos := pos, text := errorMsg };
   modify (fun s => { parser := { messages := s.parser.messages.add msg, .. s.parser }, .. s })

def getPos (stx : Syntax) : Elab String.Pos :=
match stx.getPos with
| some p => pure p
| none   => do s ← get; pure s.parser.pos

def logError (stx : Syntax) (errorMsg : String) : Elab Unit :=
do pos ← getPos stx;
   logErrorAt pos errorMsg

def logErrorAndThrow {α : Type} (stx : Syntax) (errorMsg : String) : Elab α :=
do logError stx errorMsg;
   throw (ElabException.other errorMsg)

def elabTerm (stx : Syntax) : Elab Expr :=
match stx with
| Syntax.node k _ => do
  s ← get;
  let tables := termElabAttribute.ext.getState s.env;
  match tables.find k with
  | some elab => elab stx
  | none      => logErrorAndThrow stx ("term elaborator failed, no support for syntax '" ++ toString k ++ "'")
| _ => throw (ElabException.other "term elaborator failed, unexpected syntax")

def elabCommand (stx : Syntax) : Elab Unit :=
match stx with
| Syntax.node k _ => do
  s ← get;
  let tables := commandElabAttribute.ext.getState s.env;
  match tables.find k with
  | some elab => elab stx
  | none      => logErrorAndThrow stx ("command elaborator failed, no support for syntax '" ++ toString k ++ "'")
| _ => throw (ElabException.other "command elaborator failed, unexpected syntax")

def mkElabState (env : Environment) (parser : Parser.ModuleParser) : ElabState :=
{ env := env, parser := parser }

def updateParser (p : Parser.ModuleParser) : Elab Unit :=
modify (fun s => { parser := p, .. s })

def processCommand : Elab Bool :=
do s ← get;
   let p   := s.parser;
   let pos := p.pos;
   match Parser.parseCommand s.env p with
   | (stx, p) => do
     if Parser.isEOI stx || Parser.isExitCommand stx then do
       updateParser p;
       pure true -- Done
     else do
       elabCommand stx;
       updateParser p;
       pure false

partial def processCommandsAux : Unit → Elab Unit
| () := do
  done ← processCommand;
  if done then pure ()
  else processCommandsAux ()

def processCommands : Elab Unit :=
processCommandsAux ()

def processHeader (header : Syntax) (messages : MessageLog) : IO (Option Environment × MessageLog) :=
do IO.println header;
   -- TODO
   pure (none, messages)

def testFrontend (input : String) (filename := "<input>") : IO (Option Environment × MessageLog) :=
do env ← mkEmptyEnvironment;
   let (stx, p) := Parser.mkModuleParser env input filename;
   match stx with
   | none => pure (none, p.messages)
   | some stx => do
     (optEnv, messages) ← processHeader stx p.messages;
     match optEnv with
     | none => pure (none, messages)
     | some env =>
       let p := { messages := messages, .. p };
       let s := mkElabState env p;
       match processCommands.run s with
       | EState.Result.ok _ s    => pure (some s.env, s.parser.messages)
       | EState.Result.error _ s => pure (none, s.parser.messages)

namespace Elab

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
