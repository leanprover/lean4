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

-- could be variable as well, but right now it's all names
abbrev Key := Name

variable (Value : Type)

/--
`KeyedDeclsAttribute` definition.

 Important: `mkConst valueTypeName` and `Value` must be definitionally equal. -/
structure Def (Value : Type) :=
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

structure AttributeEntry extends OLeanEntry :=
/- Recall that we cannot store `Value` into .olean files because it is a closure.
   Given `OLeanEntry.decl`, we convert it into a `Value` by using the unsafe function `evalConstCheck`. -/
(value : Value)

abbrev Table := SMap Key (List Value)

structure ExtensionState :=
(newEntries : List OLeanEntry := [])
(table      : Table Value := {})

abbrev Extension := PersistentEnvExtension OLeanEntry (AttributeEntry Value) (ExtensionState Value)

structure KeyedDeclsAttribute :=
(builtinTableRef : IO.Ref (Table Value))
(ext             : Extension Value)

variable {Value}
variable (df : Def Value)

def Table.insert (table : Table Value) (k : Key) (v : Value) : Table Value :=
match table.find? k with
| some vs => table.insert k (v::vs)
| none    => table.insert k [v]

instance ExtensionState.inhabited : Inhabited (ExtensionState Value) :=
⟨{}⟩

instance inhabited : Inhabited (KeyedDeclsAttribute Value) := ⟨{ builtinTableRef := arbitrary _, ext := arbitrary _ }⟩

private def mkInitial (builtinTableRef : IO.Ref (Table Value)) : IO (ExtensionState Value) := do
table ← builtinTableRef.get;
pure { table := table }

private unsafe def addImported (builtinTableRef : IO.Ref (Table Value)) (env : Environment) (es : Array (Array OLeanEntry)) : IO (ExtensionState Value) := do
table ← builtinTableRef.get;
table ← es.foldlM
  (fun table entries =>
    entries.foldlM
      (fun (table : Table Value) entry =>
        match env.evalConstCheck Value df.valueTypeName entry.decl with
        | Except.ok f     => pure $ table.insert entry.key f
        | Except.error ex => throw (IO.userError ex))
      table)
  table;
pure { table := table }

private def addExtensionEntry (s : ExtensionState Value) (e : AttributeEntry Value) : ExtensionState Value :=
{ table := s.table.insert e.key e.value, newEntries := e.toOLeanEntry :: s.newEntries }

def addBuiltin (attr : KeyedDeclsAttribute Value) (key : Key) (val : Value) : IO Unit :=
attr.builtinTableRef.modify $ fun m => m.insert key val

/--
def _regBuiltin$(declName) : IO Unit :=
addBuiltin $(mkConst valueTypeName) $(mkConst attrDeclName) $(key) $(mkConst declName)
-/
def declareBuiltin (attrDeclName : Name) (env : Environment) (key : Key) (declName : Name) : IO Environment :=
let name := `_regBuiltin ++ declName;
let type := mkApp (mkConst `IO) (mkConst `Unit);
let val  := mkAppN (mkConst `Lean.KeyedDeclsAttribute.addBuiltin) #[mkConst df.valueTypeName, mkConst attrDeclName, toExpr key, mkConst declName];
let decl := Declaration.defnDecl { name := name, lparams := [], type := type, value := val, hints := ReducibilityHints.opaque, isUnsafe := false };
match env.addAndCompile {} decl with
-- TODO: pretty print error
| Except.error e => throw (IO.userError ("failed to emit registration code for builtin '" ++ toString declName ++ "': " ++ toString (format $ e.toMessageData {})))
| Except.ok env  => IO.ofExcept (setInitAttr env name)

/- TODO: add support for scoped attributes -/
protected unsafe def init (attrDeclName : Name) : IO (KeyedDeclsAttribute Value) := do
builtinTableRef : IO.Ref (Table Value) ← IO.mkRef {};
ext : Extension Value ← registerPersistentEnvExtension {
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
    match env.evalConstCheck Value df.valueTypeName constName with
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
