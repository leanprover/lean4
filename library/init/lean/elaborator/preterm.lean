/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.lean.elaborator.basic

namespace Lean

abbrev PreTerm := Expr

abbrev PreTermElab := SyntaxNode → Elab PreTerm

abbrev PreTermElabTable : Type := HashMap SyntaxNodeKind PreTermElab

def mkBuiltinPreTermElabTable : IO (IO.Ref PreTermElabTable) :=  IO.mkRef {}

@[init mkBuiltinPreTermElabTable]
constant builtinPreTermElabTable : IO.Ref PreTermElabTable := default _

def addBuiltinPreTermElab (k : SyntaxNodeKind) (declName : Name) (elab : PreTermElab) : IO Unit :=
do m ← builtinPreTermElabTable.get;
   when (m.contains k) $
     throw (IO.userError ("invalid builtin term elaborator, elaborator for '" ++ toString k ++ "' has already been defined"));
   builtinPreTermElabTable.modify $ fun m => m.insert k elab

def declareBuiltinPreTermElab (env : Environment) (kind : SyntaxNodeKind) (declName : Name) : IO Environment :=
declareBuiltinElab env `Lean.addBuiltinTermElab kind declName

@[init] def registerBuiltinPreTermElabAttr : IO Unit :=
registerAttribute {
 name  := `builtinPreTermElab,
 descr := "Builtin preterm conversion elaborator, we use it to interface with the Lean3 elaborator",
 add   := fun env declName arg persistent => do {
   unless persistent $ throw (IO.userError ("invalid attribute 'builtinPreTermElab', must be persistent"));
   kind ← syntaxNodeKindOfAttrParam env `Lean.Parser.Term arg;
   match env.find declName with
   | none  => throw "unknown declaration"
   | some decl =>
     match decl.type with
     | Expr.const `Lean.PreTermElab _ => declareBuiltinPreTermElab env kind declName
     | _ => throw (IO.userError ("unexpected preterm elaborator type at '" ++ toString declName ++ "' `PreTermElab` expected"))
 },
 applicationTime := AttributeApplicationTime.afterCompilation
}

end Lean
