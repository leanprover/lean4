module

import Lean.Environment

/-!
Uses the `Lean` package through a *private* `import`, so downstream modules do not see `Lean` in
this module's public interface.
-/

public def checkEmptyEnv : IO Bool := do
  let env ← Lean.mkEmptyEnvironment
  return (env.find? `Nat).isNone
