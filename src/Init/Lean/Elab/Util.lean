/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Util.Trace
import Init.Lean.Parser

namespace Lean
namespace Elab

def checkSyntaxNodeKind (k : Name) : IO Name := do
b ← Parser.isValidSyntaxNodeKind k;
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

structure ElabAttributeEntry :=
(kind     : SyntaxNodeKind)
(declName : Name)

structure ElabAttribute (σ : Type) :=
(attr : AttributeImpl)
(ext  : PersistentEnvExtension ElabAttributeEntry σ)
(kind : String)

instance ElabAttribute.inhabited {σ} [Inhabited σ] : Inhabited (ElabAttribute σ) := ⟨{ attr := arbitrary _, ext := arbitrary _, kind := "" }⟩

/-
This is just the basic skeleton for attributes such as `[termElab]` and `[commandElab]` attributes, and associated environment extensions.
The state is initialized using `builtinTable`.

The current implementation just uses the bultin elaborators.
-/
def mkElabAttribute {σ} [Inhabited σ] (attrName : Name) (kind : String) (builtinTable : IO.Ref σ) : IO (ElabAttribute σ) := do
ext : PersistentEnvExtension ElabAttributeEntry σ ← registerPersistentEnvExtension {
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

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab;
registerTraceClass `Elab.step

end Elab
end Lean
