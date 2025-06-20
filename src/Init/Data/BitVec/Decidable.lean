/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Harun Khan, Alex Keizer, Abdalrhman M Mohamed, Siddharth Bhat

-/
module

prelude
import Init.Data.BitVec.Bootstrap

set_option linter.missingDocs true

namespace BitVec

/-! ### Decidable quantifiers -/

theorem forall_zero_iff {P : BitVec 0 → Prop} :
    (∀ v, P v) ↔ P 0#0 := by
  constructor
  · intro h
    apply h
  · intro h v
    obtain (rfl : v = 0#0) := (by ext i ⟨⟩)
    apply h

theorem forall_cons_iff {P : BitVec (n + 1) → Prop} :
    (∀ v : BitVec (n + 1), P v) ↔ (∀ (x : Bool) (v : BitVec n), P (v.cons x)) := by
  constructor
  · intro h _ _
    apply h
  · intro h v
    have w : v = (v.setWidth n).cons v.msb := by simp only [cons_msb_setWidth]
    rw [w]
    apply h

instance instDecidableForallBitVecZero (P : BitVec 0 → Prop) :
    ∀ [Decidable (P 0#0)], Decidable (∀ v, P v)
  | .isTrue h => .isTrue fun v => by
    obtain (rfl : v = 0#0) := (by ext i ⟨⟩)
    exact h
  | .isFalse h => .isFalse (fun w => h (w _))

instance instDecidableForallBitVecSucc (P : BitVec (n+1) → Prop) [DecidablePred P]
    [Decidable (∀ (x : Bool) (v : BitVec n), P (v.cons x))] : Decidable (∀ v, P v) :=
  decidable_of_iff' (∀ x (v : BitVec n), P (v.cons x)) forall_cons_iff

instance instDecidableExistsBitVecZero (P : BitVec 0 → Prop) [Decidable (P 0#0)] :
    Decidable (∃ v, P v) :=
  decidable_of_iff (¬ ∀ v, ¬ P v) Classical.not_forall_not

instance instDecidableExistsBitVecSucc (P : BitVec (n+1) → Prop) [DecidablePred P]
    [Decidable (∀ (x : Bool) (v : BitVec n), ¬ P (v.cons x))] : Decidable (∃ v, P v) :=
  decidable_of_iff (¬ ∀ v, ¬ P v) Classical.not_forall_not

/--
For small numerals this isn't necessary (as typeclass search can use the above two instances),
but for large numerals this provides a shortcut.
Note, however, that for large numerals the decision procedure may be very slow,
and you should use `bv_decide` if possible.
-/
instance instDecidableForallBitVec :
    ∀ (n : Nat) (P : BitVec n → Prop) [DecidablePred P], Decidable (∀ v, P v)
  | 0, _, _ => inferInstance
  | n + 1, _, _ =>
    have := instDecidableForallBitVec n
    inferInstance

/--
For small numerals this isn't necessary (as typeclass search can use the above two instances),
but for large numerals this provides a shortcut.
Note, however, that for large numerals the decision procedure may be very slow.
-/
instance instDecidableExistsBitVec :
    ∀ (n : Nat) (P : BitVec n → Prop) [DecidablePred P], Decidable (∃ v, P v)
  | 0, _, _ => inferInstance
  | _ + 1, _, _ => inferInstance

end BitVec
