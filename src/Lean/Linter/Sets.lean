/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

prelude
public meta import Lean.Linter.Basic
public meta import Lean.Elab.Command
public import Init.Notation
import Lean.Data.KVMap

public section

namespace Lean.Linter

/-- Add a new linter set that contains the given linters. -/
meta def insertLinterSet [MonadEnv m] (setName : Name) (linterNames : NameSet) : m Unit :=
  modifyEnv (linterSetsExt.addEntry · (setName, linterNames))

/-- `registerSet` wraps `registerOption` by setting relevant values. -/
meta def registerSet (setName : Name) (ref : Name := by exact decl_name%) : IO (Lean.Option Bool) := do
  registerOption setName {
    name := setName
    declName := ref
    defValue := false
    descr := ""
  }
  return { name := setName, defValue := false }

open Lean.Elab.Command in
/-- Declare a new linter set by giving the set of options that will be enabled along with the set. -/
elab doc?:(docComment)? "register_linter_set" name:ident " := " decl:ident* : command => do
  insertLinterSet name.getId <| decl.foldl (init := ∅) fun names name => names.insert name.getId
  let initializer ← `($[$doc?]? meta initialize $name : Lean.Option Bool ← Lean.Linter.registerSet $(quote name.getId))
  withMacroExpansion (← getRef) initializer <| elabCommand initializer


end Lean.Linter
