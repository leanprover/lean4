import Lean

/-!
Constants added on an environment branch get increasing generations (`Environment.constAddedGen`);
imported constants have generation 0, and registering a constant again keeps its generation.
-/

open Lean

def a := 1
def b := 2
theorem c : True := trivial

/-- info: imported 0, a < b < c ≤ constGen: true -/
#guard_msgs in
#eval show CoreM Unit from do
  let env ← getEnv
  let gen := env.constAddedGen
  logInfo m!"imported {gen ``Nat.add}, a < b < c ≤ constGen: \
    {decide (0 < gen ``a ∧ gen ``a < gen ``b ∧ gen ``b < gen ``c ∧ gen ``c ≤ env.constGen)}"

/-- info: kept: true, counter +1 -/
#guard_msgs in
#eval show CoreM Unit from do
  let env ← getEnv
  let env₁ := env.registerConstAdded `x
  let env₂ := env₁.registerConstAdded `x
  logInfo m!"kept: {env₂.constAddedGen `x == env₁.constAddedGen `x}, \
    counter +{env₂.constGen - env.constGen}"
