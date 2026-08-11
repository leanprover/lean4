/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Data.Int.Basic
public section
namespace Lean.Grind

/-!
Embedding classes for the `grind` tactic. A homomorphism set that targets one of the
domains natively supported by `grind`'s linear integer arithmetic solver states its
rules through the class function (`toInt` or `toNat`). The applications of these
functions are the markers the solver tracks: it assigns them variables and uses their
values for model-based theory combination. A homomorphism set that does not use them
still gets rewriting support, but no model-based theory combination.
-/

/-- `α` can be embedded into `Int` for the `grind` tactic. -/
class ToInt (α : Type u) where
  /-- The embedding function. -/
  toInt : α → Int

/-- `α` can be embedded into `Nat` for the `grind` tactic. -/
class ToNat (α : Type u) where
  /-- The embedding function. -/
  toNat : α → Nat

/- For pretty-printing purposes only. -/
@[app_unexpander ToInt.toInt]
meta def toIntUnexpander : PrettyPrinter.Unexpander := fun stx => do
  match stx with
  | `($_ $a:term) => `(↑$a)
  | _ => throw ()

/- For pretty-printing purposes only. -/
@[app_unexpander ToNat.toNat]
meta def toNatUnexpander : PrettyPrinter.Unexpander := fun stx => do
  match stx with
  | `($_ $a:term) => `(↑$a)
  | _ => throw ()

end Lean.Grind
