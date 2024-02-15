/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Lean.Elab.ElabRules
open Lean Elab Parser Term Meta Macro

/-!
Defines variants of `have` and `let` syntax which do not produce `let_fun` or `let` bindings,
but instead inline the value instead.

This is useful to declare local instances and proofs in theorem statements
and subgoals, where the extra binding is inconvenient.
-/
