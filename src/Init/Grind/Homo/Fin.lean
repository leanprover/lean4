/-
Copyright (c) 2026 Andres Erbsen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Erbsen, Leonardo de Moura
-/
module
prelude
import Init.Grind.Attr
public import Init.Data.Fin.Lemmas
public import Init.Data.Fin.Bitwise
public section

/-!
Homomorphism rules for `Fin` used by the `grind` tactic.
The injection function is `Fin.val`.
-/

attribute [grind homo]
  Fin.val_add Fin.val_mul Fin.val_sub Fin.val_mod Fin.val_zero Fin.val_succ Fin.val_neg'
  Fin.div_val Fin.and_val Fin.or_val Fin.xor_val Fin.shiftLeft_val Fin.shiftRight_val
  Fin.val_ofNat Fin.le_def Fin.lt_def

@[grind homo] theorem Lean.Grind.Fin.eq_iff_val_eq {n : Nat} (a b : Fin n) : a = b ↔ a.val = b.val :=
  ⟨Fin.val_eq_of_eq, Fin.eq_of_val_eq⟩

@[grind homo] theorem Lean.Grind.Fin.val_ite {n : Nat} (c : Prop) [Decidable c] (x y : Fin n) :
    (if c then x else y).val = if c then x.val else y.val := by
  split <;> rfl

/-! Homomorphism predicate: the range fact for `Fin.val`, instantiated by `grind` for
the terms it internalizes. -/

attribute [grind homo_pred] Fin.isLt
