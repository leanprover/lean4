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

def checkSyntaxNodeKind (env : Environment) (k : Name) : ExceptT String Id Name :=
if Parser.isValidSyntaxNodeKind env k then pure k
else throw "failed"

def checkSyntaxNodeKindAtNamespaces (env : Environment) (k : Name) : List Name → ExceptT String Id Name
| []    => throw "failed"
| n::ns => checkSyntaxNodeKind env (n ++ k) <|> checkSyntaxNodeKindAtNamespaces ns

def syntaxNodeKindOfAttrParam (env : Environment) (parserNamespace : Name) (arg : Syntax) : ExceptT String Id SyntaxNodeKind :=
match attrParamSyntaxToIdentifier arg with
| some k =>
  checkSyntaxNodeKind env k
  <|>
  checkSyntaxNodeKindAtNamespaces env k env.getNamespaces
  <|>
  checkSyntaxNodeKind env (parserNamespace ++ k)
  <|>
  throw ("invalid syntax node kind '" ++ toString k ++ "'")
| none   => throw ("syntax node kind is missing")

structure ElabAttributeOLeanEntry :=
(kind      : SyntaxNodeKind)
(constName : Name)

structure ElabAttributeEntry (γ : Type) extends ElabAttributeOLeanEntry :=
(elabFn   : γ)

abbrev ElabFnTable (γ : Type) := SMap SyntaxNodeKind (List γ)

def ElabFnTable.insert {γ} (table : ElabFnTable γ) (k : SyntaxNodeKind) (f : γ) : ElabFnTable γ :=
match table.find? k with
| some fs => table.insert k (f::fs)
| none    => table.insert k [f]

structure ElabAttributeExtensionState (γ : Type) :=
(newEntries : List ElabAttributeOLeanEntry := [])
(table      : ElabFnTable γ                := {})

instance ElabAttributeExtensionState.inhabited (γ) : Inhabited (ElabAttributeExtensionState γ) :=
⟨{}⟩

abbrev ElabAttributeExtension (γ) := PersistentEnvExtension ElabAttributeOLeanEntry (ElabAttributeEntry γ) (ElabAttributeExtensionState γ)

structure ElabAttribute (γ : Type) :=
(attr : AttributeImpl)
(ext  : ElabAttributeExtension γ)
(kind : String)

instance ElabAttribute.inhabited {γ} : Inhabited (ElabAttribute γ) := ⟨{ attr := arbitrary _, ext := arbitrary _, kind := "" }⟩

private def ElabAttribute.mkInitial {γ} (builtinTableRef : IO.Ref (ElabFnTable γ)) : IO (ElabAttributeExtensionState γ) := do
table ← builtinTableRef.get;
pure { table := table }

private def throwUnexpectedElabType {γ} (typeName : Name) (constName : Name) : ExceptT String Id γ :=
throw ("unexpected elaborator type at '" ++ toString constName ++ "', `" ++ toString typeName ++ "` expected")

private unsafe def mkElabFnOfConstantUnsafe (γ) (env : Environment) (typeName : Name) (constName : Name) : ExceptT String Id γ :=
match env.find? constName with
| none      => throw ("unknow constant '" ++ toString constName ++ "'")
| some info =>
  match info.type with
  | Expr.const c _ _ =>
    if c != typeName then throwUnexpectedElabType typeName constName
    else env.evalConst γ constName
  | _ => throwUnexpectedElabType typeName constName

@[implementedBy mkElabFnOfConstantUnsafe]
constant mkElabFnOfConstant (γ : Type) (env : Environment) (typeName : Name) (constName : Name) : ExceptT String Id γ := throw ""

private def ElabAttribute.addImportedParsers {γ} (typeName : Name) (builtinTableRef : IO.Ref (ElabFnTable γ))
    (env : Environment) (es : Array (Array ElabAttributeOLeanEntry)) : IO (ElabAttributeExtensionState γ) := do
table ← builtinTableRef.get;
table ← es.foldlM
  (fun table entries =>
    entries.foldlM
      (fun (table : ElabFnTable γ) entry =>
        match mkElabFnOfConstant γ env typeName entry.constName with
        | Except.ok f     => pure $ table.insert entry.kind f
        | Except.error ex => throw (IO.userError ex))
      table)
  table;
pure { table := table }

private def ElabAttribute.addExtensionEntry {γ} (s : ElabAttributeExtensionState γ) (e : ElabAttributeEntry γ) : ElabAttributeExtensionState γ :=
{ table := s.table.insert e.kind e.elabFn, newEntries := e.toElabAttributeOLeanEntry :: s.newEntries }

private def ElabAttribute.add {γ} (parserNamespace : Name) (typeName : Name) (ext : ElabAttributeExtension γ)
    (env : Environment) (constName : Name) (arg : Syntax) (persistent : Bool) : IO Environment := do
match mkElabFnOfConstant γ env typeName constName with
| Except.error ex => throw (IO.userError ex)
| Except.ok f     => do
  kind ← IO.ofExcept $ syntaxNodeKindOfAttrParam env parserNamespace arg;
  pure $ ext.addEntry env { kind := kind, elabFn := f, constName := constName }

/- TODO: add support for scoped attributes -/
def mkElabAttribute (γ) (attrName : Name) (parserNamespace : Name) (typeName : Name) (kind : String) (builtinTableRef : IO.Ref (ElabFnTable γ)) : IO (ElabAttribute γ) := do
ext : ElabAttributeExtension γ ← registerPersistentEnvExtension {
  name            := attrName,
  mkInitial       := ElabAttribute.mkInitial builtinTableRef,
  addImportedFn   := ElabAttribute.addImportedParsers typeName builtinTableRef,
  addEntryFn      := ElabAttribute.addExtensionEntry,
  exportEntriesFn := fun s => s.newEntries.reverse.toArray,
  statsFn         := fun s => format "number of local entries: " ++ format s.newEntries.length
};
let attrImpl : AttributeImpl := {
  name            := attrName,
  descr           := kind ++ " elaborator",
  add             := ElabAttribute.add parserNamespace typeName ext,
  applicationTime := AttributeApplicationTime.afterCompilation
};
registerAttribute attrImpl;
pure { ext := ext, attr := attrImpl, kind := kind }

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab;
registerTraceClass `Elab.step

end Elab
end Lean
