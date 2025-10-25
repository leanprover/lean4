/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lean.Data.NameMap.Basic

open Lean Syntax Parser Command

namespace Lake

public structure ConfigProj (σ : Type u) (α : Type v) where
  get (cfg : σ) : α
  set (val : α) (cfg : σ) : σ
  modify (f : α → α) (cfg : σ) : σ
  mkDefault : σ → α

public class ConfigField (σ : Type u) (name : Name) (α : outParam $ Type v) extends ConfigProj σ α

public abbrev mkFieldDefault (name : Name) [field : ConfigField σ name α] (cfg : σ) : α :=
  field.mkDefault cfg

public class ConfigParent (σ : Type u) (ρ : semiOutParam $ Type v) extends ConfigProj σ ρ

public structure ConfigFieldInfo where
  /-- The name of the field (possibly an alias). -/
  name : Name
  /-- The real name of the field in the configuration structure. -/
  realName : Name
  /-- Whether `name == realName` and the field is not a parent projection. -/
  canonical : Bool := false
  /-- Whether the field is a parent projection. -/
  parent : Bool := false

public class ConfigFields (σ : Type u) where
  fields : Array ConfigFieldInfo

public class ConfigInfo (name : Name) where
  fields : Array ConfigFieldInfo
  fieldMap : NameMap ConfigFieldInfo :=
    fields.foldl (init := ∅) fun m i => m.insert i.name i
  arity : Nat

public instance [parent : ConfigParent σ ρ] [field : ConfigField ρ name α] : ConfigField σ name α where
  mkDefault s := field.mkDefault (parent.get s)
  get s := field.get (parent.get s)
  set a := parent.modify (field.set a)
  modify f := parent.modify (field.modify f)
