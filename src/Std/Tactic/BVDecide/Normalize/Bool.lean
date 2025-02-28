/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Init.SimpLemmas
import Init.Data.Bool
import Init.Data.BitVec.Lemmas

/-!
This module contains the `Bool` simplifying part of the `bv_normalize` simp set.
-/

namespace Std.Tactic.BVDecide
namespace Normalize

attribute [bv_normalize] Bool.not_true
attribute [bv_normalize] Bool.not_false
attribute [bv_normalize] Bool.and_true
attribute [bv_normalize] Bool.true_and
attribute [bv_normalize] Bool.and_false
attribute [bv_normalize] Bool.false_and
attribute [bv_normalize] Bool.true_beq
attribute [bv_normalize] beq_true
attribute [bv_normalize] Bool.false_beq
attribute [bv_normalize] beq_false
attribute [bv_normalize] Bool.beq_not_self
attribute [bv_normalize] Bool.not_beq_self
attribute [bv_normalize] Bool.beq_self_left
attribute [bv_normalize] Bool.beq_self_right
attribute [bv_normalize] Bool.and_self
attribute [bv_normalize] Bool.and_not_self
attribute [bv_normalize] Bool.not_and_self
attribute [bv_normalize] Bool.xor_self
attribute [bv_normalize] Bool.xor_false
attribute [bv_normalize] Bool.false_xor
attribute [bv_normalize] Bool.true_xor
attribute [bv_normalize] Bool.xor_true
attribute [bv_normalize] Bool.not_xor_self
attribute [bv_normalize] Bool.xor_not_self
attribute [bv_normalize] Bool.not_not
attribute [bv_normalize] Bool.and_self_left
attribute [bv_normalize] Bool.and_self_right
attribute [bv_normalize] Bool.cond_self
attribute [bv_normalize] Bool.cond_not

@[bv_normalize]
theorem if_eq_cond {b : Bool} {x y : α} : (if b = true then x else y) = (bif b then x else y) := by
  rw [cond_eq_if]

@[bv_normalize]
theorem Bool.not_xor : ∀ (a b : Bool), !(a ^^ b) = (a == b) := by decide

@[bv_normalize]
theorem Bool.or_elim : ∀ (a b : Bool), (a || b) = !(!a && !b) := by decide

@[bv_normalize]
theorem Bool.not_beq_one : ∀ (a : BitVec 1), (!(a == 1#1)) = (a == 0#1) := by
  decide

@[bv_normalize]
theorem Bool.not_beq_zero : ∀ (a : BitVec 1), (!(a == 0#1)) = (a == 1#1) := by
  decide

@[bv_normalize]
theorem Bool.not_one_beq : ∀ (a : BitVec 1), (!(1#1 == a)) = (a == 0#1) := by
  decide

@[bv_normalize]
theorem Bool.not_zero_beq : ∀ (a : BitVec 1), (!(0#1 == a)) = (a == 1#1) := by
  decide

@[bv_normalize]
theorem Bool.ite_same_then : ∀ (c t e : Bool), ((bif c then t else e) == t) = (c || (t == e)) := by
  decide

@[bv_normalize]
theorem Bool.ite_same_then' : ∀ (c t e : Bool), (t == (bif c then t else e)) = (c || (t == e)) := by
  decide

@[bv_normalize]
theorem Bool.ite_same_else : ∀ (c t e : Bool), ((bif c then t else e) == e) = (!c || (t == e)) := by
  decide

@[bv_normalize]
theorem Bool.ite_same_else' :
    ∀ (c t e : Bool), (e == (bif c then t else e)) = (!c || (t == e)) := by
  decide

@[bv_normalize]
theorem BitVec.ite_same_then :
    ∀ (c : Bool) (t e : BitVec w), ((bif c then t else e) == t) = (c || (t == e)) := by
  intro c t e
  cases c <;> simp [BEq.comm (a := t) (b := e)]

@[bv_normalize]
theorem BitVec.ite_same_then' :
    ∀ (c : Bool) (t e : BitVec w), (t == (bif c then t else e)) = (c || (t == e)) := by
  intro c t e
  cases c <;> simp

@[bv_normalize]
theorem BitVec.ite_same_else :
    ∀ (c : Bool) (t e : BitVec w), ((bif c then t else e) == e) = (!c || (t == e)) := by
  intro c t e
  cases c <;> simp

@[bv_normalize]
theorem BitVec.ite_same_else' :
    ∀ (c : Bool) (t e : BitVec w), (e == (bif c then t else e)) = (!c || (t == e)) := by
  intro c t e
  cases c <;> simp [BEq.comm (a := t) (b := e)]

theorem Bool.and_left (lhs rhs : Bool) (h : (lhs && rhs) = true) : lhs = true := by
  revert lhs rhs
  decide

theorem Bool.and_right (lhs rhs : Bool) (h : (lhs && rhs) = true) : rhs = true := by
  revert lhs rhs
  decide

end Normalize
end Std.Tactic.BVDecide

