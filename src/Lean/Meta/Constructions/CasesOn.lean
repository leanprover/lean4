/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.AddDecl
import Lean.Meta.Basic

namespace Lean

@[extern "lean_mk_cases_on"] opaque mkCasesOnImp (env : Environment) (declName : @& Name) : Except KernelException Declaration

open Meta

def mkCasesOn (declName : Name) : MetaM Unit := do
  let name := mkCasesOnName declName
  let decl ← ofExceptKernelException (mkCasesOnImp (← getEnv) declName)
  addDecl decl
  setReducibleAttribute name
  modifyEnv fun env => markAuxRecursor env name

end Lean
