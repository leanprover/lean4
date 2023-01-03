/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Compiler.InitAttr
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
  /-- Builtin attribute name, if any (e.g., `builtin_term_elab) -/
  builtinName   : Name := Name.anonymous
  /-- Attribute name (e.g., `term_elab) -/
  name          : Name
  /-- Attribute description -/
  descr         : String
  valueTypeName : Name
  /-- Convert `Syntax` into a `Key`, the default implementation expects an identifier. -/
  evalKey (builtin : Bool) (stx : Syntax) : AttrM Key := do
    let stx ← Attribute.Builtin.getIdent stx
    let kind := stx.getId
    if (← getEnv).contains kind && (← Elab.getInfoState).enabled then
      Elab.addConstInfo stx kind none
    pure kind
  onAdded (builtin : Bool) (declName : Name) : AttrM Unit := pure ()
  deriving Inhabited

structure OLeanEntry where
  key      : Key
  /-- Name of a declaration stored in the environment which has type `mkConst Def.valueTypeName`. -/
  declName : Name
  deriving Inhabited

structure AttributeEntry (γ : Type) extends OLeanEntry where
  /-- Recall that we cannot store `γ` into .olean files because it is a closure.
     Given `OLeanEntry.declName`, we convert it into a `γ` by using the unsafe function `evalConstCheck`. -/
  value : γ

abbrev Table (γ : Type) := SMap Key (List (AttributeEntry γ))

structure ExtensionState (γ : Type) where
  newEntries : List OLeanEntry := []
  table      : Table γ := {}
  declNames  : PHashSet Name := {}
  erased     : PHashSet Name := {}
  deriving Inhabited

abbrev Extension (γ : Type) := ScopedEnvExtension OLeanEntry (AttributeEntry γ) (ExtensionState γ)

end KeyedDeclsAttribute

structure KeyedDeclsAttribute (γ : Type) where
  defn : KeyedDeclsAttribute.Def γ
  -- imported/builtin instances
  tableRef : IO.Ref (KeyedDeclsAttribute.Table γ)
  -- instances from current module
  ext : KeyedDeclsAttribute.Extension γ
  deriving Nonempty

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

protected unsafe def init {γ} (df : Def γ) (attrDeclName : Name := by exact decl_name%) : IO (KeyedDeclsAttribute γ) := do
  let tableRef ← IO.mkRef ({} : Table γ)
  let ext : Extension γ ← registerScopedEnvExtension {
    name         := attrDeclName
    mkInitial    := return mkStateOfTable (← tableRef.get)
    ofOLeanEntry := fun _ entry => do
      let ctx ← read
      match ctx.env.evalConstCheck γ ctx.opts df.valueTypeName entry.declName with
      | Except.ok f     => return { toOLeanEntry := entry, value := f }
      | Except.error ex => throw (IO.userError ex)
    addEntry     := fun s e => s.insert e
    toOLeanEntry := (·.toOLeanEntry)
  }
  unless df.builtinName.isAnonymous do
    registerBuiltinAttribute {
      ref   := attrDeclName
      name  := df.builtinName
      descr := "(builtin) " ++ df.descr
      add   := fun declName stx kind => do
        unless kind == AttributeKind.global do throwError "invalid attribute '{df.builtinName}', must be global"
        let key ← df.evalKey true stx
        let decl ← getConstInfo declName
        match decl.type with
        | Expr.const c _ =>
          if c != df.valueTypeName then throwError "unexpected type at '{declName}', '{df.valueTypeName}' expected"
          else
            /- builtin_initialize @addBuiltin $(mkConst valueTypeName) $(mkConst attrDeclName) $(key) $(declName) $(mkConst declName) -/
            let val := mkAppN (mkConst ``addBuiltin) #[mkConst df.valueTypeName, mkConst attrDeclName, toExpr key, toExpr declName, mkConst declName]
            declareBuiltin declName val
            df.onAdded true declName
        | _ => throwError "unexpected type at '{declName}', '{df.valueTypeName}' expected"
      applicationTime := AttributeApplicationTime.afterCompilation
    }
  registerBuiltinAttribute {
    ref             := attrDeclName
    name            := df.name
    descr           := df.descr
    erase           := fun declName => do
      let s := ext.getState (← getEnv)
      let s ← s.erase df.name declName
      modifyEnv fun env => ext.modifyState env fun _ => s
    add             := fun declName stx attrKind => do
      let key ← df.evalKey false stx
      match IR.getSorryDep (← getEnv) declName with
      | none =>
        let val ← evalConstCheck γ df.valueTypeName declName
        ext.add { key := key, declName := declName, value := val } attrKind
        df.onAdded false declName
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
