/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Lean.Attributes

open Lean
namespace Lake

structure OrderedTagAttribute where
  attr : AttributeImpl
  ext  : PersistentEnvExtension Name Name (Array Name)
  deriving Inhabited

def registerOrderedTagAttribute (name : Name) (descr : String)
    (validate : Name → AttrM Unit := fun _ => pure ()) (ref : Name := by exact decl_name%) : IO OrderedTagAttribute := do
  let ext ← registerPersistentEnvExtension {
    name            := ref
    mkInitial       := pure {}
    addImportedFn   := fun _ _ => pure {}
    addEntryFn      := fun s n => s.push n
    exportEntriesFn := fun es => es
    statsFn         := fun s => "tag attribute" ++ Format.line ++ "number of local entries: " ++ format s.size
  }
  let attrImpl : AttributeImpl := {
    ref   := ref
    name  := name
    descr := descr
    add   := fun decl stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do throwError "invalid attribute '{name}', must be global"
      let env ← getEnv
      unless (env.getModuleIdxFor? decl).isNone do
        throwError "invalid attribute '{name}', declaration is in an imported module"
      validate decl
      modifyEnv fun env => ext.addEntry env decl
  }
  registerBuiltinAttribute attrImpl
  return { attr := attrImpl, ext }

def OrderedTagAttribute.hasTag (attr : OrderedTagAttribute) (env : Environment) (decl : Name) : Bool :=
  match env.getModuleIdxFor? decl with
  | some modIdx => (attr.ext.getModuleEntries env modIdx).binSearchContains decl Name.quickLt
  | none        => (attr.ext.getState env).contains decl

/-- Get all tagged declaration names, both those imported and those in the current module. -/
def OrderedTagAttribute.getAllEntries (attr : OrderedTagAttribute) (env : Environment) : Array Name :=
  let s := attr.ext.toEnvExtension.getState env
  s.importedEntries.flatMap id ++ s.state
