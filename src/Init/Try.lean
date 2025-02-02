/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Tactics

namespace Lean.Try
/--
Configuration for `try?`.
-/
structure Config where
  /--
  If `core` is `true`, then constants in the `Init` and `Std` library are considered for unfolding.
  This flag is used for debugging purposes only.
  -/
  core := false
  deriving Inhabited


end Lean.Try

namespace Lean.Parser.Tactic

syntax (name := tryTrace) "try?" optConfig : tactic

end Lean.Parser.Tactic
