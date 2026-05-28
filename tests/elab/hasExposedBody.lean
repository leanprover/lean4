module
import Lean.Elab.Command

/-!
# Tests for `Lean.Environment.hasExposedBody`

Confirms the function returns `true` only for `def`s whose body is exposed across
module boundaries, and `false` for theorems, opaques, axioms, inductives,
declarations not in the environment, and `def`s whose body is sealed by the
module system.
-/

@[expose] def exposedDef : Nat := 0
def sealedDef : Nat := 1
theorem aTheorem : 0 = 0 := rfl
opaque anOpaque : Nat := 2
axiom anAxiom : Nat
inductive AnInductive where | mk

run_cmd do
  let env ← Lean.getEnv
  guard <| env.hasExposedBody ``exposedDef
  guard <| !env.hasExposedBody ``sealedDef
  guard <| !env.hasExposedBody ``aTheorem
  guard <| !env.hasExposedBody ``anOpaque
  guard <| !env.hasExposedBody ``anAxiom
  guard <| !env.hasExposedBody ``AnInductive
  guard <| !env.hasExposedBody `nonexistent.name
