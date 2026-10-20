module
import Lean.Elab.Command

/-!
# Tests for `Lean.Environment.hasExposedBody`

Confirms the function returns `true` only for `def`s whose body is exposed across
module boundaries, and `false` for theorems, opaques, axioms, inductives,
declarations not in the environment, and `def`s whose body is sealed by the
module system.
-/

@[expose] public def exposedDef : Nat := 0
def sealedDef : Nat := 1
theorem aTheorem : 0 = 0 := rfl
opaque anOpaque : Nat := 2
axiom anAxiom : Nat
inductive AnInductive where | mk

run_cmd do
  let env ← Lean.getEnv
  unless env.hasExposedBody ``exposedDef do
    throwError "`exposedDef` should have an exposed body"
  for n in [``sealedDef, ``aTheorem, ``anOpaque, ``anAxiom, ``AnInductive, `nonexistent.name] do
    if env.hasExposedBody n then
      throwError "`{n}` should not have an exposed body"
