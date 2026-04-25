/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Lean.Compiler.ModPkgExt

public section

namespace Lean

structure DeprecatedModuleEntry where
  message? : Option String := none
  since? : Option String := none
  deriving Inhabited

register_builtin_option linter.deprecated.module : Bool := {
  defValue := true
  descr := "if true, generate warnings when importing deprecated modules"
}

builtin_initialize deprecatedModuleExt : ModuleEnvExtension <| Option DeprecatedModuleEntry ←
  registerModuleEnvExtension <| pure none

def Environment.getDeprecatedModuleByIdx? (env : Environment) (idx : ModuleIdx) : Option DeprecatedModuleEntry :=
  deprecatedModuleExt.getStateByIdx? env idx |>.join

def Environment.setDeprecatedModule (entry : Option DeprecatedModuleEntry) (env : Environment) : Environment :=
  deprecatedModuleExt.setState env entry

def formatDeprecatedModuleWarning (env : Environment) (idx : ModuleIdx) (modName : Name)
    (entry : DeprecatedModuleEntry) : String :=
  let msg := entry.message?.getD ""
  let replacements := env.header.moduleData[idx.toNat]!.imports.filter fun imp =>
    imp.module != `Init
  let lines := replacements.foldl (init := "") fun acc imp =>
    acc ++ s!"import {imp.module}\n"
  s!"{msg}\n\
    '{modName}' has been deprecated: please replace this import by\n\n\
    {lines}"

end Lean
