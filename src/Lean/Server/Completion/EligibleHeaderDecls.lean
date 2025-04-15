/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
prelude
import Lean.Meta.CompletionName

namespace Lean.Server.Completion
open Meta

abbrev EligibleHeaderDecls := Std.HashMap Name ConstantInfo

/-- Cached header declarations for which `allowCompletion headerEnv decl` is true. -/
builtin_initialize eligibleHeaderDeclsRef : IO.Ref (Option EligibleHeaderDecls) ←
  IO.mkRef none

/--
Returns the declarations in the header for which `allowCompletion env decl` is true, caching them
if not already cached.
-/
def getEligibleHeaderDecls (env : Environment) : IO EligibleHeaderDecls := do
  eligibleHeaderDeclsRef.modifyGet fun
    | some eligibleHeaderDecls => (eligibleHeaderDecls, some eligibleHeaderDecls)
    | none =>
      let (_, eligibleHeaderDecls) :=
        StateT.run (m := Id) (s := {}) do
          -- `map₁` are the header decls
          env.constants.map₁.forM fun declName c => do
            modify fun eligibleHeaderDecls =>
              if allowCompletion env declName then
                eligibleHeaderDecls.insert declName c
              else
                eligibleHeaderDecls
      (eligibleHeaderDecls, some eligibleHeaderDecls)

/-- Iterate over all declarations that are allowed in completion results. -/
def forEligibleDeclsM [Monad m] [MonadEnv m] [MonadLiftT (ST IO.RealWorld) m]
    [MonadLiftT IO m] (f : Name → ConstantInfo → m PUnit) : m PUnit := do
  let env ← getEnv
  (← getEligibleHeaderDecls env).forM f
  -- map₂ are exactly the local decls
  env.constants.map₂.forM fun name c => do
    if allowCompletion env name then
      f name c

/-- Checks whether this declaration can appear in completion results. -/
def allowCompletion (eligibleHeaderDecls : EligibleHeaderDecls) (env : Environment)
    (declName : Name) : Bool :=
  eligibleHeaderDecls.contains declName ||
    env.constants.map₂.contains declName && Lean.Meta.allowCompletion env declName

end Lean.Server.Completion
