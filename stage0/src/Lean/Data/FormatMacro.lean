#lang lean4
/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Data.Format
namespace Lean

syntax:max "f!" (interpolatedStr term) : term

macro_rules
| `(f! $interpStr) => do
  let chunks := interpStr.getArgs
  let r ← Lean.Syntax.expandInterpolatedStrChunks chunks (fun a b => `($a ++ $b)) (fun a => `(fmt $a))
  `(($r : Format))

end Lean
