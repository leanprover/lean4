/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Attributes
import Init.Lean.Compiler.InitAttr
import Init.Lean.ToExpr
import Init.Lean.Meta.Message

/-!
A builder for attributes that are applied to declarations of a common type and
group them by the given attribute argument (an arbitrary `Name`, currently).
Also creates a second "builtin" attribute used for bootstrapping, which saves
the applied declarations in an `IO.Ref` instead of an environment extension.

Used to register elaborators, macros, tactics, and delaborators.
-/

namespace Lean
namespace KeyedDeclsAttribute

-- could be a parameter as well, but right now it's all names
abbrev Key := Name

/--
`KeyedDeclsAttribute` definition.

 Important: `mkConst valueTypeName` and `γ` must be definitionally equal. -/
structure Def (γ : Type) :=
(builtinName   : Name)    -- Builtin attribute name (e.g., `builtinTermElab)
(name          : Name)    -- Attribute name (e.g., `termElab)
(descr         : String)  -- Attribute description
(valueTypeName : Name)
-- Convert `Syntax` into a `Key`, the default implementation expects an identifier.
(evalKey       : Environment → Syntax → Except String Key :=
  fun env arg => match attrParamSyntaxToIdentifier arg with
    | some id => Except.ok id
    | none    => Except.error "invalid attribute argument, expected identifier")

structure OLeanEntry :=
(key  : Key)
(decl : Name) -- Name of a declaration stored in the environment which has type `mkConst Def.valueTypeName`.

structure AttributeEntry (γ : Type) extends OLeanEntry :=
/- Recall that we cannot store `γ` into .olean files because it is a closure.
   Given `OLeanEntry.decl`, we convert it into a `γ` by using the unsafe function `evalConstCheck`. -/
(value : γ)

abbrev Table (γ : Type) := SMap Key (List γ)

structure ExtensionState (γ : Type) :=
(newEntries : List OLeanEntry := [])
(table      : Table γ := {})

abbrev Extension (γ : Type) := PersistentEnvExtension OLeanEntry (AttributeEntry γ) (ExtensionState γ)

structure KeyedDeclsAttribute (γ : Type) :=
(builtinTableRef : IO.Ref (Table γ))
(ext             : Extension γ)

def Table.insert {γ : Type} (table : Table γ) (k : Key) (v : γ) : Table γ :=
match table.find? k with
| some vs => table.insert k (v::vs)
| none    => table.insert k [v]

instance ExtensionState.inhabited {γ} : Inhabited (ExtensionState γ) :=
⟨{}⟩

instance KeyedDeclsAttribute.inhabited {γ} : Inhabited (KeyedDeclsAttribute γ) :=
⟨{ builtinTableRef := arbitrary _, ext := arbitrary _ }⟩

private def mkInitial {γ} (builtinTableRef : IO.Ref (Table γ)) : IO (ExtensionState γ) := do
table ← builtinTableRef.get;
pure { table := table }

private unsafe def addImported {γ} (df : Def γ) (builtinTableRef : IO.Ref (Table γ)) (env : Environment) (es : Array (Array OLeanEntry)) : IO (ExtensionState γ) := do
table ← builtinTableRef.get;
table ← es.foldlM
  (fun table entries =>
    entries.foldlM
      (fun (table : Table γ) entry =>
        match env.evalConstCheck γ df.valueTypeName entry.decl with
        | Except.ok f     => pure $ table.insert entry.key f
        | Except.error ex => throw (IO.userError ex))
      table)
  table;
pure { table := table }

private def addExtensionEntry {γ} (s : ExtensionState γ) (e : AttributeEntry γ) : ExtensionState γ :=
{ table := s.table.insert e.key e.value, newEntries := e.toOLeanEntry :: s.newEntries }

def addBuiltin {γ} (attr : KeyedDeclsAttribute γ) (key : Key) (val : γ) : IO Unit :=
attr.builtinTableRef.modify $ fun m => m.insert key val

/--
def _regBuiltin$(declName) : IO Unit :=
addBuiltin $(mkConst valueTypeName) $(mkConst attrDeclName) $(key) $(mkConst declName)
-/
def declareBuiltin {γ} (df : Def γ) (attrDeclName : Name) (env : Environment) (key : Key) (declName : Name) : IO Environment :=
let name := `_regBuiltin ++ declName;
let type := mkApp (mkConst `IO) (mkConst `Unit);
let val  := mkAppN (mkConst `Lean.KeyedDeclsAttribute.addBuiltin) #[mkConst df.valueTypeName, mkConst attrDeclName, toExpr key, mkConst declName];
let decl := Declaration.defnDecl { name := name, lparams := [], type := type, value := val, hints := ReducibilityHints.opaque, isUnsafe := false };
match env.addAndCompile {} decl with
-- TODO: pretty print error
| Except.error e => throw (IO.userError ("failed to emit registration code for builtin '" ++ toString declName ++ "': " ++ toString (format $ e.toMessageData {})))
| Except.ok env  => IO.ofExcept (setInitAttr env name)

/- TODO: add support for scoped attributes -/
protected unsafe def init {γ} (df : Def γ) (attrDeclName : Name) : IO (KeyedDeclsAttribute γ) := do
builtinTableRef : IO.Ref (Table γ) ← IO.mkRef {};
ext : Extension γ ← registerPersistentEnvExtension {
  name            := df.name,
  mkInitial       := mkInitial builtinTableRef,
  addImportedFn   := addImported df builtinTableRef,
  addEntryFn      := addExtensionEntry,
  exportEntriesFn := fun s => s.newEntries.reverse.toArray,
  statsFn         := fun s => format "number of local entries: " ++ format s.newEntries.length
};
registerBuiltinAttribute {
 name  := df.builtinName,
 descr := "(builtin) " ++ df.descr,
 add   := fun env declName arg persistent => do {
   unless persistent $ throw (IO.userError ("invalid attribute '" ++ toString df.builtinName ++ "', must be persistent"));
   key ← IO.ofExcept $ df.evalKey env arg;
   match env.find? declName with
   | none  => throw $ IO.userError "unknown declaration"
   | some decl =>
     match decl.type with
     | Expr.const c _ _ =>
       if c != df.valueTypeName then throw (IO.userError ("unexpected type at '" ++ toString declName ++ "', `" ++ toString df.valueTypeName ++ "` expected"))
       else declareBuiltin df attrDeclName env key declName
     | _ => throw (IO.userError ("unexpected type at '" ++ toString declName ++ "', `" ++ toString df.valueTypeName ++ "` expected"))
 },
 applicationTime := AttributeApplicationTime.afterCompilation
};
registerBuiltinAttribute {
  name            := df.name,
  descr           := df.descr,
  add             := fun env constName arg persistent =>
    match env.evalConstCheck γ df.valueTypeName constName with
    | Except.error ex => throw (IO.userError ex)
    | Except.ok v     => do
      key ← IO.ofExcept $ df.evalKey env arg;
      pure $ ext.addEntry env { key := key, decl := constName, value := v },
  applicationTime := AttributeApplicationTime.afterCompilation
};
pure { builtinTableRef := builtinTableRef, ext := ext }

end KeyedDeclsAttribute

export KeyedDeclsAttribute (KeyedDeclsAttribute)

end Lean
