module

import Lean
import all Init.Prelude

/-! Docstrings from .olean.server should be visible even on the cmdline when `import all`ed. -/

open Lean

/-- info: true -/
#guard_msgs in
#eval show MetaM _ from return (← findDocString? (← getEnv) ``Nat).isSome
