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

/- We currently cannot mark the following definition as an instance since it increases the search space too much -/
def monadEnvFromLift (m) {n} [MonadEnv m] [HasMonadLiftT m n] : MonadEnv n :=
{ getEnv    := liftM (getEnv : m Environment),
  modifyEnv := fun f => liftM (modifyEnv f : m Unit) }

instance ReaderT.monadEnv {m ρ} [Monad m] [MonadEnv m] : MonadEnv (ReaderT ρ m) := monadEnvFromLift m
instance StateRefT.monadEnv {m σ} [MonadEnv m] : MonadEnv (StateRefT σ m)   := monadEnvFromLift m
instance OptionT.monadEnv {m} [Monad m] [MonadEnv m] : MonadEnv (OptionT m) := monadEnvFromLift m

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
