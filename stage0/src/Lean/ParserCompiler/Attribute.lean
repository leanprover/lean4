/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/

import Lean.Attributes
import Lean.Compiler.InitAttr
import Lean.ToExpr

namespace Lean
namespace ParserCompiler

structure CombinatorAttribute :=
  (impl : AttributeImpl)
  (ext  : SimplePersistentEnvExtension (Name × Name) (NameMap Name))

-- TODO(Sebastian): We'll probably want priority support here at some point

def registerCombinatorAttribute (name : Name) (descr : String)
    : IO CombinatorAttribute := do
  let ext : SimplePersistentEnvExtension (Name × Name) (NameMap Name) ← registerSimplePersistentEnvExtension {
    name            := name,
    addImportedFn   := mkStateFromImportedEntries (fun s p => s.insert p.1 p.2) {},
    addEntryFn      := fun (s : NameMap Name) (p : Name × Name) => s.insert p.1 p.2,
  }
  let attrImpl : AttributeImpl := {
    name  := name,
    descr := descr,
    add   := fun decl args _ => do
      let env ← getEnv
      match attrParamSyntaxToIdentifier args with
      | some parserDeclName => do
        getConstInfo parserDeclName
        setEnv <| ext.addEntry env (parserDeclName, decl)
      | none            => throwError! "invalid [{name}] argument, expected identifier"
  }
  registerBuiltinAttribute attrImpl
  pure { impl := attrImpl, ext := ext }

namespace CombinatorAttribute

instance : Inhabited CombinatorAttribute := ⟨{ impl := arbitrary, ext := arbitrary }⟩

def getDeclFor? (attr : CombinatorAttribute) (env : Environment) (parserDecl : Name) : Option Name :=
  (attr.ext.getState env).find? parserDecl

def setDeclFor (attr : CombinatorAttribute) (env : Environment) (parserDecl : Name) (decl : Name) : Environment :=
  attr.ext.addEntry env (parserDecl, decl)

unsafe def runDeclFor {α} (attr : CombinatorAttribute) (parserDecl : Name) : CoreM α := do
  match attr.getDeclFor? (← getEnv) parserDecl with
  | some d => evalConst α d
  | _      => throwError! "no declaration of attribute [{attr.impl.name}] found for '{parserDecl}'"

end CombinatorAttribute

end ParserCompiler
end Lean
