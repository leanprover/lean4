/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Attributes
import Lean.Compiler.InitAttr
import Lean.ToExpr
import Lean.ScopedEnvExtension
import Lean.Compiler.IR.CompilerM

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
  key      : Key
  declName : Name -- Name of a declaration stored in the environment which has type `mkConst Def.valueTypeName`.
  deriving Inhabited

structure AttributeEntry (γ : Type) extends OLeanEntry where
  /- Recall that we cannot store `γ` into .olean files because it is a closure.
     Given `OLeanEntry.declName`, we convert it into a `γ` by using the unsafe function `evalConstCheck`. -/
  value : γ

abbrev Table (γ : Type) := SMap Key (List (AttributeEntry γ))

structure ExtensionState (γ : Type) where
  newEntries : List OLeanEntry := []
  table      : Table γ := {}
  declNames  : Std.PHashSet Name := {}
  erased     : Std.PHashSet Name := {}
  deriving Inhabited

abbrev Extension (γ : Type) := ScopedEnvExtension OLeanEntry (AttributeEntry γ) (ExtensionState γ)

end KeyedDeclsAttribute

structure KeyedDeclsAttribute (γ : Type) where
  defn : KeyedDeclsAttribute.Def γ
  -- imported/builtin instances
  tableRef : IO.Ref (KeyedDeclsAttribute.Table γ)
  -- instances from current module
  ext      : KeyedDeclsAttribute.Extension γ
  deriving Inhabited

namespace KeyedDeclsAttribute

private def Table.insert (table : Table γ) (v : AttributeEntry γ) : Table γ :=
  match table.find? v.key with
  | some vs => SMap.insert table v.key (v::vs)
  | none    => SMap.insert table v.key [v]

def ExtensionState.insert (s : ExtensionState γ) (v : AttributeEntry γ) :  ExtensionState γ := {
  table      := s.table.insert v
  newEntries := v.toOLeanEntry :: s.newEntries
  declNames  := s.declNames.insert v.declName
  erased     := s.erased.erase v.declName
}

def addBuiltin (attr : KeyedDeclsAttribute γ) (key : Key) (declName : Name) (value : γ) : IO Unit :=
  attr.tableRef.modify fun m => m.insert { key, declName, value }

def mkStateOfTable (table : Table γ) : ExtensionState γ := {
  table
  declNames := table.fold (init := {}) fun s _ es => es.foldl (init := s) fun s e => s.insert e.declName
}

def ExtensionState.erase (s : ExtensionState γ) (attrName : Name) (declName : Name) : CoreM (ExtensionState γ) := do
  unless s.declNames.contains declName do
    throwError "'{declName}' does not have [{attrName}] attribute"
  return { s with erased := s.erased.insert declName, declNames := s.declNames.erase declName }

/--
def _regBuiltin$(declName) : IO Unit :=
@addBuiltin $(mkConst valueTypeName) $(mkConst attrDeclName) $(key) $(declName) $(mkConst declName)
-/
def declareBuiltin {γ} (df : Def γ) (attrDeclName : Name) (env : Environment) (key : Key) (declName : Name) : IO Environment :=
  let name := `_regBuiltin ++ declName
  let type := mkApp (mkConst `IO) (mkConst `Unit)
  let val  := mkAppN (mkConst `Lean.KeyedDeclsAttribute.addBuiltin) #[mkConst df.valueTypeName, mkConst attrDeclName, toExpr key, toExpr declName, mkConst declName]
  let decl := Declaration.defnDecl { name := name, levelParams := [], type := type, value := val, hints := ReducibilityHints.opaque,
                                     safety := DefinitionSafety.safe }
  match env.addAndCompile {} decl with
  -- TODO: pretty print error
  | Except.error e => do
    let msg ← (e.toMessageData {}).toString
    throw (IO.userError s!"failed to emit registration code for builtin '{declName}': {msg}")
  | Except.ok env  => IO.ofExcept (setBuiltinInitAttr env name)

protected unsafe def init {γ} (df : Def γ) (attrDeclName : Name) : IO (KeyedDeclsAttribute γ) := do
  let tableRef ← IO.mkRef ({} : Table γ)
  let ext : Extension γ ← registerScopedEnvExtension {
    name         := df.name
    mkInitial    := return mkStateOfTable (← tableRef.get)
    ofOLeanEntry := fun s entry => do
      let ctx ← read
      match ctx.env.evalConstCheck γ ctx.opts df.valueTypeName entry.declName with
      | Except.ok f     => return { toOLeanEntry := entry, value := f }
      | Except.error ex => throw (IO.userError ex)
    addEntry     := fun s e => s.insert e
    toOLeanEntry := (·.toOLeanEntry)
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
    name            := df.name
    descr           := df.descr
    erase           := fun declName => do
      let s ← ext.getState (← getEnv)
      let s ← s.erase df.name declName
      modifyEnv fun env => ext.modifyState env fun _ => s
    add             := fun declName stx attrKind => do
      let key ← df.evalKey false stx
      match IR.getSorryDep (← getEnv) declName with
      | none =>
        let val ← evalConstCheck γ df.valueTypeName declName
        ext.add { key := key, declName := declName, value := val } attrKind
      | _ =>
        -- If the declaration contains `sorry`, we skip `evalConstCheck` to avoid unnecessary bizarre error message
        pure ()
    applicationTime := AttributeApplicationTime.afterCompilation
  }
  pure { defn := df, tableRef := tableRef, ext := ext }

/-- Retrieve entries tagged with `[attr key]` or `[builtinAttr key]`. -/
def getEntries {γ} (attr : KeyedDeclsAttribute γ) (env : Environment) (key : Name) : List (AttributeEntry γ) :=
  let s := attr.ext.getState env
  let attrs := s.table.findD key []
  if s.erased.isEmpty then
    attrs
  else
    attrs.filter fun attr => !s.erased.contains attr.declName

/-- Retrieve values tagged with `[attr key]` or `[builtinAttr key]`. -/
def getValues {γ} (attr : KeyedDeclsAttribute γ) (env : Environment) (key : Name) : List γ :=
  (getEntries attr env key).map AttributeEntry.value

end KeyedDeclsAttribute

end Lean
