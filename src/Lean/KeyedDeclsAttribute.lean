/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Attributes
import Lean.Compiler.InitAttr
import Lean.ToExpr
import Lean.Meta.Message

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
(builtinName   : Option Name)  -- Builtin attribute name (e.g., `builtinTermElab)
(name          : Name)         -- Attribute name (e.g., `termElab)
(descr         : String)       -- Attribute description
(valueTypeName : Name)
-- Evaluate the given constant. Uses `Environment.evalConstCheck` by default, but that is unsafe, so we
-- don't specify it here.
(evalValue     : Option (Environment → Name → IO γ) := none)
-- Compile the given constant. Evaluating the resulting term should result in the same value as using
-- `evalValue`.
(compileValue  : Environment → Name → IO Expr := fun env declName => do
  match env.find? declName with
  | none  => throw $ IO.userError "unknown declaration"
  | some decl =>
    match decl.type with
    | Expr.const c _ _ =>
      if c != valueTypeName then throw (IO.userError ("unexpected type at '" ++ toString declName ++ "', `" ++ toString valueTypeName ++ "` expected"))
      else pure (mkConst declName)
    | _ => throw (IO.userError ("unexpected type at '" ++ toString declName ++ "', `" ++ toString valueTypeName ++ "` expected")))
-- Convert `Syntax` into a `Key`, the default implementation expects an identifier.
(evalKey       : Environment → Syntax → Except String Key :=
  fun env arg => match attrParamSyntaxToIdentifier arg with
    | some id => Except.ok id
    | none    => Except.error "invalid attribute argument, expected identifier")

/-- Build a `KeyedDeclsAttribute` definition that merely stores names of tagged declarations without interpreting them. -/
def Def.mkSimple (builtinName : Option Name) (name : Name) (descr : String) : Def Name :=
{ builtinName := builtinName,
  name        := name,
  descr       := descr,
  valueTypeName := `Lean.Name,
  evalValue   := some fun env declName => pure declName,
  compileValue := fun env declName => pure (toExpr declName) }

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

end KeyedDeclsAttribute

structure KeyedDeclsAttribute (γ : Type) :=
-- imported/builtin instances
(tableRef : IO.Ref (KeyedDeclsAttribute.Table γ))
-- instances from current module
(ext      : KeyedDeclsAttribute.Extension γ)

namespace KeyedDeclsAttribute

def Table.insert {γ : Type} (table : Table γ) (k : Key) (v : γ) : Table γ :=
match table.find? k with
| some vs => table.insert k (v::vs)
| none    => table.insert k [v]

instance ExtensionState.inhabited {γ} : Inhabited (ExtensionState γ) :=
⟨{}⟩

instance KeyedDeclsAttribute.inhabited {γ} : Inhabited (KeyedDeclsAttribute γ) :=
⟨{ tableRef := arbitrary _, ext := arbitrary _ }⟩

private def mkInitial {γ} (tableRef : IO.Ref (Table γ)) : IO (ExtensionState γ) := do
table ← tableRef.get;
pure { table := table }

private unsafe def evalValue {γ} (df : Def γ) (env : Environment) (constName : Name) : IO γ :=
match df.evalValue with
  | some eval => eval env constName
  | none      => match env.evalConstCheck γ df.valueTypeName constName with
    | Except.error ex => throw (IO.userError ex)
    | Except.ok v     => pure v

private unsafe def addImported {γ} (df : Def γ) (tableRef : IO.Ref (Table γ)) (env : Environment) (es : Array (Array OLeanEntry)) : IO (ExtensionState γ) := do
table ← tableRef.get;
table ← es.foldlM
  (fun table entries =>
    entries.foldlM
      (fun (table : Table γ) entry => do
        val ← evalValue df env entry.decl;
        pure $ table.insert entry.key val)
      table)
  table;
pure { table := table }

private def addExtensionEntry {γ} (s : ExtensionState γ) (e : AttributeEntry γ) : ExtensionState γ :=
{ table := s.table.insert e.key e.value, newEntries := e.toOLeanEntry :: s.newEntries }

def addBuiltin {γ} (attr : KeyedDeclsAttribute γ) (key : Key) (val : γ) : IO Unit :=
attr.tableRef.modify $ fun m => m.insert key val

/--
def _regBuiltin$(declName) : IO Unit :=
@addBuiltin $(mkConst valueTypeName) $(mkConst attrDeclName) $(key) $(val)
-/
def declareBuiltin {γ} (df : Def γ) (attrDeclName : Name) (env : Environment) (key : Key) (declName : Name) : IO Environment := do
let name := `_regBuiltin ++ declName;
let type := mkApp (mkConst `IO) (mkConst `Unit);
val ← df.compileValue env declName;
let val  := mkAppN (mkConst `Lean.KeyedDeclsAttribute.addBuiltin) #[mkConst df.valueTypeName, mkConst attrDeclName, toExpr key, val];
let decl := Declaration.defnDecl { name := name, lparams := [], type := type, value := val, hints := ReducibilityHints.opaque, isUnsafe := false };
match env.addAndCompile {} decl with
-- TODO: pretty print error
| Except.error e => throw (IO.userError ("failed to emit registration code for builtin '" ++ toString declName ++ "': " ++ toString (format $ e.toMessageData {})))
| Except.ok env  => IO.ofExcept (setInitAttr env name)

/- TODO: add support for scoped attributes -/
protected unsafe def init {γ} (df : Def γ) (attrDeclName : Name) : IO (KeyedDeclsAttribute γ) := do
tableRef : IO.Ref (Table γ) ← IO.mkRef {};
ext : Extension γ ← registerPersistentEnvExtension {
  name            := df.name,
  mkInitial       := mkInitial tableRef,
  addImportedFn   := addImported df tableRef,
  addEntryFn      := addExtensionEntry,
  exportEntriesFn := fun s => s.newEntries.reverse.toArray,
  statsFn         := fun s => format "number of local entries: " ++ format s.newEntries.length
};
match df.builtinName with
| some builtinName =>
  registerBuiltinAttribute {
    name  := builtinName,
    descr := "(builtin) " ++ df.descr,
    add   := fun env declName arg persistent => do {
      unless persistent $ throw (IO.userError ("invalid attribute '" ++ toString df.builtinName ++ "', must be persistent"));
      key ← IO.ofExcept $ df.evalKey env arg;
      declareBuiltin df attrDeclName env key declName
    },
    applicationTime := AttributeApplicationTime.afterCompilation
  }
| _ => pure ();
registerBuiltinAttribute {
  name            := df.name,
  descr           := df.descr,
  add             := fun env constName arg persistent => do
    key ← IO.ofExcept $ df.evalKey env arg;
    val ← evalValue df env constName;
    pure $ ext.addEntry env { key := key, decl := constName, value := val },
  applicationTime := AttributeApplicationTime.afterCompilation
};
pure { tableRef := tableRef, ext := ext }

/-- Retrieve values tagged with `[attr key]` or `[builtinAttr key]`. -/
def getValues {γ} (attr : KeyedDeclsAttribute γ) (env : Environment) (key : Name) : List γ :=
(attr.ext.getState env).table.findD key []

end KeyedDeclsAttribute

end Lean
