/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.Decl

namespace Lean.Compiler

structure Stage1ExtState where
  decls : Std.PHashMap Name Decl := {}
  deriving Inhabited

builtin_initialize stage1Ext : EnvExtension Stage1ExtState ←
  registerEnvExtension (pure {})

/- "Forward declaration" -/
@[extern "lean_compile_stage1"]
opaque compileStage1 : Array Name → CoreM (Array Decl)

/--
Save/Cache the given LCNF declarations in the stage1 environment extension.
-/
def saveStage1Decls (decls : Array Decl) : CoreM Unit :=
  modifyEnv fun env => stage1Ext.modifyState env fun s => decls.foldl (init := s) fun s decl =>
    { s with decls := s.decls.insert decl.name decl }

/--
Retrieve stage1 LCNF declaration for the given declaration.

We currently do not store stage1 declarations on .olean files,
and we generate
-/
def getStage1Decl? (declName : Name) : CoreM (Option Decl) := do
  match stage1Ext.getState (← getEnv) |>.decls.find? declName with
  | some decl => return decl
  | none =>
    let info ← getConstInfo declName
    let decls ← compileStage1 info.all.toArray
    return decls.find? fun decl => declName == decl.name

end Lean.Compiler