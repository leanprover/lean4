/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.lean.namegenerator
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

def declareBuiltinTermElab (env : Environment) (kind : Name) (declName : Name) : IO Environment :=
pure env
/-
TODO

let name := `_regBuiltinTermElab ++ declName;
let type := Expr.app (mkConst `IO) (mkConst `Unit);
let val  := mkCApp addFnName [mkConst refDeclName, toExpr declName, mkConst declName];
let decl := Declaration.defnDecl { name := name, lparams := [], type := type, value := val, hints := ReducibilityHints.opaque, isUnsafe := false };
match env.addAndCompile {} decl with
| none     => throw (IO.userError ("failed to emit registration code for builtin parser '" ++ toString declName ++ "'"))
| some env => IO.ofExcept (setInitAttr env name)
-/

@[init] def registerBuiltinTermElabAttr : IO Unit :=
registerAttribute {
 name  := `builtinTermElab,
 descr := "Builtin term elaborator",
 add   := fun env declName args persistent => do {
   unless persistent $ throw (IO.userError ("invalid attribute 'builtinTermElab', must be persistent"));
   match env.find declName with
   | none  => throw "unknown declaration"
   | some decl =>
     match decl.type with
     | Expr.const `Lean.TermElab _ => declareBuiltinTermElab env `kind declName
     | _ => throw (IO.userError ("unexpected term elaborator type at '" ++ toString declName ++ "' `TermElab` expected"))
 },
 applicationTime := AttributeApplicationTime.afterCompilation
}

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
