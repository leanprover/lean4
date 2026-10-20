module

import Foo

/-!
Regression test: this executable root does not visibly import `Lean` (it is only privately imported
by `Foo`), but the linked binary still contains and initializes `Lean` code, so the generated code
must fully initialize the Lean runtime (`lean_initialize`) before running `main`. Getting this
wrong makes the executable crash at startup.
-/

public def main : IO Unit := do
  IO.println s!"empty env has no Nat: {← checkEmptyEnv}"
