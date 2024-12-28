/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Tactics

namespace Lean.Grind
/--
The configuration for `grind`.
Passed to `grind` using, for example, the `grind (config := { eager := true })` syntax.
-/
structure Config where
  /--
  When `eager` is true (default: `false`), `grind` eagerly splits `if-then-else` and `match`
  expressions.
  -/
  eager : Bool := false
  deriving Inhabited, BEq

end Lean.Grind

namespace Lean.Parser.Tactic

/-!
`grind` tactic and related tactics.
-/

-- TODO: configuration option, parameters
syntax (name := grind) "grind" : tactic

end Lean.Parser.Tactic
