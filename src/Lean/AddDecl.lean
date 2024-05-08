/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.ReducibilityAttrs

namespace Lean

def Environment.addDecl (env : Environment) (opts : Options) (decl : Declaration) : Except KernelException Environment :=
  let decl := setReducibilityHintsOverride env opts decl
  addDeclCore env decl

def Environment.addAndCompile (env : Environment) (opts : Options) (decl : Declaration) : Except KernelException Environment := do
  let env ← addDecl env opts decl
  compileDecl env opts decl

def addDecl (decl : Declaration) : CoreM Unit := do
  profileitM Exception "type checking" (← getOptions) do
    withTraceNode `Kernel (fun _ => return m!"typechecking declaration") do
      if !(← MonadLog.hasErrors) && decl.hasSorry then
        logWarning "declaration uses 'sorry'"
      match (← getEnv).addDecl (← getOptions) decl with
      | .ok    env => setEnv env
      | .error ex  => throwKernelException ex

def addAndCompile (decl : Declaration) : CoreM Unit := do
  addDecl decl
  compileDecl decl

end Lean
