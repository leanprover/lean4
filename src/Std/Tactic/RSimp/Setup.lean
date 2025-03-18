/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
prelude
import Lean.Meta.Tactic.Simp.RegisterCommand

/--
The `rsimp` simp set is used by the `rsimp_decide` tactic to optimize terms for kernel reduction.

It is separate from the default simp set because they have different normal forms. For example
`simp` wants to replae concrete operations like `Nat.add` with the overloaded `+`, but for
efficient reduction, we want to go the other way.
-/
register_simp_attr rsimp
