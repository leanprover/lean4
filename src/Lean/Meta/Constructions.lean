/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Environment
import Lean.MonadEnv

namespace Lean

@[extern "lean_mk_cases_on"] constant mkCasesOnImp (env : Environment) (declName : @& Name) : Except KernelException Environment
@[extern "lean_mk_rec_on"] constant mkRecOnImp (env : Environment) (declName : @& Name) : Except KernelException Environment
@[extern "lean_mk_no_confusion"] constant mkNoConfusionImp (env : Environment) (declName : @& Name) : Except KernelException Environment
@[extern "lean_mk_below"] constant mkBelowImp (env : Environment) (declName : @& Name) : Except KernelException Environment
@[extern "lean_mk_ibelow"] constant mkIBelowImp (env : Environment) (declName : @& Name) : Except KernelException Environment
@[extern "lean_mk_brec_on"] constant mkBRecOnImp (env : Environment) (declName : @& Name) : Except KernelException Environment
@[extern "lean_mk_binduction_on"] constant mkBInductionOnImp (env : Environment) (declName : @& Name) : Except KernelException Environment

variable {m} [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m]

@[inline] private def adaptFn (f : Environment → Name → Except KernelException Environment) (declName : Name) : m Unit := do
  match f (← getEnv) declName with
  | Except.ok env   => modifyEnv fun _ => env
  | Except.error ex => throwKernelException ex

def mkCasesOn (declName : Name) : m Unit := adaptFn mkCasesOnImp declName
def mkRecOn (declName : Name) : m Unit := adaptFn mkRecOnImp declName
def mkNoConfusion (declName : Name) : m Unit := adaptFn mkNoConfusionImp declName
def mkBelow (declName : Name) : m Unit := adaptFn mkBelowImp declName
def mkIBelow (declName : Name) : m Unit := adaptFn mkIBelowImp declName
def mkBRecOn (declName : Name) : m Unit := adaptFn mkBRecOnImp declName
def mkBInductionOn (declName : Name) : m Unit := adaptFn mkBInductionOnImp declName

end Lean
