/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.LeanInit
import Init.Data.ToString.Basic
new_frontend

syntax:max "s!" (interpolatedStr term) : term

macro_rules
| `(s! $interpStr) => do
  let chunks := interpStr.getArgs
  let r ← Lean.Syntax.expandInterpolatedStrChunks chunks (fun a b => `($a ++ $b)) (fun a => `(toString $a))
  `(($r : String))
