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
(messages : MessageLog := {})
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

/-
Examples:

@[builtinTermElab «do»] def elabDo : TermElab :=
fun stx => pure (default Expr)

@[builtinCommandElab «open»] def elabOpen : CommandElab :=
fun stx => pure ()
-/

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
