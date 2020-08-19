/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Attributes
import Lean.Compiler.InitAttr
import Lean.ToExpr
import Lean.Meta.Message

/-!
Gadgets for compiling parser declarations into other programs, such as pretty printers.
-/

namespace Lean

structure CombinatorCompilerAttribute :=
(attr : AttributeImpl)
(ext  : SimplePersistentEnvExtension (Name × Name) (NameMap Name))

-- TODO(Sebastian): We'll probably want priority support here at some point

def registerCombinatorCompilerAttribute (name : Name) (descr : String)
    : IO CombinatorCompilerAttribute := do
ext : SimplePersistentEnvExtension (Name × Name) (NameMap Name) ← registerSimplePersistentEnvExtension {
  name            := name,
  addImportedFn   := mkStateFromImportedEntries (fun s p => s.insert p.1 p.2) {},
  addEntryFn      := fun (s : NameMap Name) (p : Name × Name) => s.insert p.1 p.2,
};
let attrImpl : AttributeImpl := {
  name  := name,
  descr := descr,
  add   := fun decl args _ => do
    env ← Core.getEnv;
    match attrParamSyntaxToIdentifier args with
    | some parserDeclName => do
      _ ← Core.getConstInfo parserDeclName;
      Core.setEnv $ ext.addEntry env (parserDeclName, decl)
    | none            => Core.throwError $ "invalid [" ++ name ++ "] argument, expected identifier"
};
registerBuiltinAttribute attrImpl;
pure { attr := attrImpl, ext := ext }

namespace CombinatorCompilerAttribute

instance : Inhabited CombinatorCompilerAttribute := ⟨{attr := arbitrary _, ext := arbitrary _}⟩

def getDeclFor (attr : CombinatorCompilerAttribute) (env : Environment) (parserDecl : Name) : Option Name :=
(attr.ext.getState env).find? parserDecl

def setDeclFor (attr : CombinatorCompilerAttribute) (env : Environment) (parserDecl : Name) (decl : Name) : Environment :=
attr.ext.addEntry env (parserDecl, decl)

end CombinatorCompilerAttribute
end Lean
