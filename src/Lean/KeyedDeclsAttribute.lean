/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Attributes
import Lean.Compiler.InitAttr
import Lean.ToExpr

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
structure Def (γ : Type) where
  builtinName   : Name := Name.anonymous  -- Builtin attribute name, if any (e.g., `builtinTermElab)
  name          : Name    -- Attribute name (e.g., `termElab)
  descr         : String  -- Attribute description
  valueTypeName : Name
  -- Convert `Syntax` into a `Key`, the default implementation expects an identifier.
  evalKey       : Bool → Syntax → AttrM Key := fun builtin stx => Attribute.Builtin.getId stx
  deriving Inhabited

structure OLeanEntry where
  key  : Key
  decl : Name -- Name of a declaration stored in the environment which has type `mkConst Def.valueTypeName`.

structure AttributeEntry (γ : Type) extends OLeanEntry where
  /- Recall that we cannot store `γ` into .olean files because it is a closure.
     Given `OLeanEntry.decl`, we convert it into a `γ` by using the unsafe function `evalConstCheck`. -/
  value : γ

abbrev Table (γ : Type) := SMap Key (List γ)

structure ExtensionState (γ : Type) where
  newEntries : List OLeanEntry := []
  table      : Table γ := {}
  deriving Inhabited

abbrev Extension (γ : Type) := PersistentEnvExtension OLeanEntry (AttributeEntry γ) (ExtensionState γ)

end KeyedDeclsAttribute

structure KeyedDeclsAttribute (γ : Type) where
  defn : KeyedDeclsAttribute.Def γ
  -- imported/builtin instances
  tableRef : IO.Ref (KeyedDeclsAttribute.Table γ)
  -- instances from current module
  ext      : KeyedDeclsAttribute.Extension γ
  deriving Inhabited

namespace KeyedDeclsAttribute

def Table.insert {γ : Type} (table : Table γ) (k : Key) (v : γ) : Table γ :=
  match table.find? k with
  | some vs => SMap.insert table k (v::vs)
  | none    => SMap.insert table k [v]

private def mkInitial {γ} (tableRef : IO.Ref (Table γ)) : IO (ExtensionState γ) := do
  let table ← tableRef.get
  pure { table := table }

private unsafe def addImported {γ} (df : Def γ) (tableRef : IO.Ref (Table γ)) (es : Array (Array OLeanEntry)) : ImportM (ExtensionState γ) := do
  let ctx ← read
  let mut table ← tableRef.get
  for entries in es do
    for entry in entries do
      match ctx.env.evalConstCheck γ ctx.opts df.valueTypeName entry.decl with
      | Except.ok f     => table := table.insert entry.key f
      | Except.error ex => throw (IO.userError ex)
  return { table := table }

private def addExtensionEntry {γ} (s : ExtensionState γ) (e : AttributeEntry γ) : ExtensionState γ :=
  { table := s.table.insert e.key e.value, newEntries := e.toOLeanEntry :: s.newEntries }

def addBuiltin {γ} (attr : KeyedDeclsAttribute γ) (key : Key) (val : γ) : IO Unit :=
  attr.tableRef.modify fun m => m.insert key val

/--
def _regBuiltin$(declName) : IO Unit :=
@addBuiltin $(mkConst valueTypeName) $(mkConst attrDeclName) $(key) $(mkConst declName)
-/
def declareBuiltin {γ} (df : Def γ) (attrDeclName : Name) (env : Environment) (key : Key) (declName : Name) : IO Environment :=
  let name := `_regBuiltin ++ declName
  let type := mkApp (mkConst `IO) (mkConst `Unit)
  let val  := mkAppN (mkConst `Lean.KeyedDeclsAttribute.addBuiltin) #[mkConst df.valueTypeName, mkConst attrDeclName, toExpr key, mkConst declName]
  let decl := Declaration.defnDecl { name := name, levelParams := [], type := type, value := val, hints := ReducibilityHints.opaque,
                                     safety := DefinitionSafety.safe }
  match env.addAndCompile {} decl with
  -- TODO: pretty print error
  | Except.error e => do
    let msg ← (e.toMessageData {}).toString
    throw (IO.userError s!"failed to emit registration code for builtin '{declName}': {msg}")
  | Except.ok env  => IO.ofExcept (setBuiltinInitAttr env name)

/- TODO: add support for scoped attributes -/
protected unsafe def init {γ} (df : Def γ) (attrDeclName : Name) : IO (KeyedDeclsAttribute γ) := do
  let tableRef ← IO.mkRef ({} : Table γ)
  let ext : Extension γ ← registerPersistentEnvExtension {
    name            := df.name,
    mkInitial       := mkInitial tableRef,
    addImportedFn   := addImported df tableRef,
    addEntryFn      := addExtensionEntry,
    exportEntriesFn := fun s => s.newEntries.reverse.toArray,
    statsFn         := fun s => f!"number of local entries: {s.newEntries.length}"
  }
  unless df.builtinName.isAnonymous do
    registerBuiltinAttribute {
      name  := df.builtinName,
      descr := "(builtin) " ++ df.descr,
      add   := fun declName stx kind => do
        unless kind == AttributeKind.global do throwError "invalid attribute '{df.builtinName}', must be global"
        let key ← df.evalKey true stx
        let decl ← getConstInfo declName
        match decl.type with
        | Expr.const c _ _ =>
          if c != df.valueTypeName then throwError "unexpected type at '{declName}', '{df.valueTypeName}' expected"
          else
            let env ← getEnv
            let env ← declareBuiltin df attrDeclName env key declName
            setEnv env
        | _ => throwError "unexpected type at '{declName}', '{df.valueTypeName}' expected",
      applicationTime := AttributeApplicationTime.afterCompilation
    }
  registerBuiltinAttribute {
    name            := df.name,
    descr           := df.descr,
    add             := fun constName stx persistent => do
      let key ← df.evalKey false stx
      let val ← evalConstCheck γ df.valueTypeName constName
      let env ← getEnv
      setEnv <| ext.addEntry env { key := key, decl := constName, value := val },
    applicationTime := AttributeApplicationTime.afterCompilation
  }
  pure { defn := df, tableRef := tableRef, ext := ext }

/-- Retrieve values tagged with `[attr key]` or `[builtinAttr key]`. -/
def getValues {γ} (attr : KeyedDeclsAttribute γ) (env : Environment) (key : Name) : List γ :=
  (attr.ext.getState env).table.findD key []

end KeyedDeclsAttribute

end Lean
