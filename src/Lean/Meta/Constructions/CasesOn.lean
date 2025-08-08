/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.AddDecl
public import Lean.Meta.Basic

public section

namespace Lean

@[extern "lean_mk_cases_on"] opaque mkCasesOnImp (env : Kernel.Environment) (declName : @& Name) : Except Kernel.Exception Declaration

open Meta

def mkCasesOn (declName : Name) : MetaM Unit := do
  let name := mkCasesOnName declName
  let decl ← ofExceptKernelException (mkCasesOnImp (← getEnv).toKernelEnv declName)
  addDecl decl
  setReducibleAttribute name
  modifyEnv fun env => markAuxRecursor env name
  enableRealizationsForConst name

end Lean
