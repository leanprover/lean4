/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Init.Control.Option
import Lean.Environment
import Lean.Exception

namespace Lean

class MonadEnv (m : Type → Type) :=
(getEnv    : m Environment)
(modifyEnv : (Environment → Environment) → m Unit)

export MonadEnv (getEnv modifyEnv)

instance monadEnvFromLift (m n) [MonadEnv m] [HasMonadLift m n] : MonadEnv n :=
{ getEnv    := liftM (getEnv : m Environment),
  modifyEnv := fun f => liftM (modifyEnv f : m Unit) }

section Methods

variables {m : Type → Type} [MonadEnv m]

def setEnv (env : Environment) : m Unit :=
modifyEnv fun _ => env

section
variables [Monad m] [MonadError m]

def getConstInfo (constName : Name) : m ConstantInfo := do
env ← getEnv;
match env.find? constName with
| some info => pure info
| none      => throwError ("unknown constant '" ++ constName ++ "'")

def addDecl [MonadOptions m] (decl : Declaration) : m Unit := do
env ← getEnv;
match env.addDecl decl with
| Except.ok    env => setEnv env
| Except.error ex  => throwKernelException ex

def compileDecl [MonadOptions m] (decl : Declaration) : m Unit := do
env  ← getEnv;
opts ← getOptions;
match env.compileDecl opts decl with
| Except.ok env   => setEnv env
| Except.error ex => throwKernelException ex

def addAndCompile [MonadOptions m] (decl : Declaration) : m Unit := do
addDecl decl;
compileDecl decl

end

end Methods
end Lean
