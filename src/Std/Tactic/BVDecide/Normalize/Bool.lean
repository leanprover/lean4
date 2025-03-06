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

@[bv_normalize]
theorem Bool.ite_then_ite (cond : Bool) {a b c : α} :
    (bif cond then (bif cond then a else b) else c) = (bif cond then a else c) := by
  cases cond <;> simp

@[bv_normalize]
theorem Bool.ite_then_not_ite (cond : Bool) {a b c : Bool} :
    (bif cond then !(bif cond then a else b) else c) = (bif cond then !a else c) := by
  cases cond <;> simp

@[bv_normalize]
theorem BitVec.ite_then_not_ite (cond : Bool) {a b c : BitVec w} :
    (bif cond then ~~~(bif cond then a else b) else c) = (bif cond then ~~~a else c) := by
  cases cond <;> simp

@[bv_normalize]
theorem Bool.ite_else_ite (cond : Bool) {a b c : α} :
    (bif cond then a else (bif cond then b else c)) = (bif cond then a else c) := by
  cases cond <;> simp

@[bv_normalize]
theorem Bool.ite_else_not_ite (cond : Bool) {a b c : Bool} :
    (bif cond then a else !(bif cond then b else c)) = (bif cond then a else !c) := by
  cases cond <;> simp

@[bv_normalize]
theorem BitVec.ite_else_not_ite (cond : Bool) {a b c : BitVec w} :
    (bif cond then a else ~~~(bif cond then b else c)) = (bif cond then a else ~~~c) := by
  cases cond <;> simp

@[bv_normalize]
theorem Bool.ite_then_ite' (c0 c1 : Bool) {a b : α} :
    (bif c0 then (bif c1 then a else b) else a) = (bif c0 && !c1 then b else a) := by
  cases c0 <;> cases c1 <;> simp

@[bv_normalize]
theorem Bool.ite_then_not_ite' (c0 c1 : Bool) {a b : Bool} :
    (bif c0 then !(bif c1 then !a else b) else a) = (bif c0 && !c1 then !b else a) := by
  cases c0 <;> cases c1 <;> simp

@[bv_normalize]
theorem BitVec.ite_then_not_ite' (c0 c1 : Bool) {a b : BitVec w} :
    (bif c0 then ~~~(bif c1 then ~~~a else b) else a) = (bif c0 && !c1 then ~~~b else a) := by
  cases c0 <;> cases c1 <;> simp

@[bv_normalize]
theorem Bool.ite_else_ite' (c0 c1 : Bool) {a b : α} :
    (bif c0 then a else (bif c1 then a else b)) = (bif !c0 && !c1 then b else a) := by
  cases c0 <;> cases c1 <;> simp

@[bv_normalize]
theorem Bool.ite_else_not_ite' (c0 c1 : Bool) {a b : Bool} :
    (bif c0 then a else !(bif c1 then !a else b)) = (bif !c0 && !c1 then !b else a) := by
  cases c0 <;> cases c1 <;> simp

@[bv_normalize]
theorem BitVec.ite_else_not_ite' (c0 c1 : Bool) {a b : BitVec w} :
    (bif c0 then a else ~~~(bif c1 then ~~~a else b)) = (bif !c0 && !c1 then ~~~b else a) := by
  cases c0 <;> cases c1 <;> simp

@[bv_normalize]
theorem Bool.ite_then_ite'' (c0 c1 : Bool) {a b : α} :
    (bif c0 then (bif c1 then b else a) else a) = (bif c0 && c1 then b else a) := by
  cases c0 <;> cases c1 <;> simp

@[bv_normalize]
theorem Bool.ite_then_not_ite'' (c0 c1 : Bool) {a b : Bool} :
    (bif c0 then !(bif c1 then b else !a) else a) = (bif c0 && c1 then !b else a) := by
  cases c0 <;> cases c1 <;> simp

@[bv_normalize]
theorem BitVec.ite_then_not_ite'' (c0 c1 : Bool) {a b : BitVec w} :
    (bif c0 then ~~~(bif c1 then b else ~~~a) else a) = (bif c0 && c1 then ~~~b else a) := by
  cases c0 <;> cases c1 <;> simp

@[bv_normalize]
theorem Bool.ite_else_ite'' (c0 c1 : Bool) {a b : α} :
    (bif c0 then a else (bif c1 then b else a)) = (bif !c0 && c1 then b else a) := by
  cases c0 <;> cases c1 <;> simp

@[bv_normalize]
theorem Bool.ite_else_not_ite'' (c0 c1 : Bool) {a b : Bool} :
    (bif c0 then a else !(bif c1 then b else !a)) = (bif !c0 && c1 then !b else a) := by
  cases c0 <;> cases c1 <;> simp

@[bv_normalize]
theorem BitVec.ite_else_not_ite'' (c0 c1 : Bool) {a b : BitVec w} :
    (bif c0 then a else ~~~(bif c1 then b else ~~~a )) = (bif !c0 && c1 then ~~~b else a) := by
  cases c0 <;> cases c1 <;> simp

@[bv_normalize]
theorem BitVec.mul_ite_zero {c : Bool} {a e : BitVec w} :
    (a * (bif c then 0#w else e)) = (bif c then 0#w else a * e) := by
  cases c <;> simp

@[bv_normalize]
theorem BitVec.mul_ite_zero' {c : Bool} {a t : BitVec w} :
    (a * (bif c then t else 0#w)) = (bif c then a * t else 0#w) := by
  cases c <;> simp

@[bv_normalize]
theorem BitVec.mul_ite_zero'' {c : Bool} {a e : BitVec w} :
    ((bif c then 0#w else e) * a) = (bif c then 0#w else e * a) := by
  cases c <;> simp

@[bv_normalize]
theorem BitVec.mul_ite_zero''' {c : Bool} {a t : BitVec w} :
    ((bif c then t else 0#w) * a) = (bif c then t * a else 0#w) := by
  cases c <;> simp

@[bv_normalize]
theorem BitVec.beq_one_eq_ite {b : Bool} {a : BitVec 1} :
    ((a == 1#1) == b) = (a == bif b then 1#1 else 0#1) := by
  decide +revert

@[bv_normalize]
theorem BitVec.one_beq_eq_ite {b : Bool} {a : BitVec 1} :
    ((1#1 == a) == b) = (a == bif b then 1#1 else 0#1) := by
  decide +revert

@[bv_normalize]
theorem BitVec.beq_one_eq_ite' {b : Bool} {a : BitVec 1} :
    (b == (a == 1#1)) = (a == bif b then 1#1 else 0#1) := by
  decide +revert

@[bv_normalize]
theorem BitVec.one_beq_eq_ite' {b : Bool} {a : BitVec 1} :
    (b == (1#1 == a)) = (a == bif b then 1#1 else 0#1) := by
  decide +revert

@[bv_normalize]
theorem BitVec.beq_zero_eq_ite {b : Bool} {a : BitVec 1} :
    ((a == 0#1) == b) = (a == bif b then 0#1 else 1#1) := by
  decide +revert

@[bv_normalize]
theorem BitVec.zero_beq_eq_ite {b : Bool} {a : BitVec 1} :
    ((0#1 == a) == b) = (a == bif b then 0#1 else 1#1) := by
  decide +revert

@[bv_normalize]
theorem BitVec.beq_zero_eq_ite' {b : Bool} {a : BitVec 1} :
    (b == (a == 0#1)) = (a == bif b then 0#1 else 1#1) := by
  decide +revert

@[bv_normalize]
theorem BitVec.zero_beq_eq_ite' {b : Bool} {a : BitVec 1} :
    (b == (0#1 == a)) = (a == bif b then 0#1 else 1#1) := by
  decide +revert

@[bv_normalize]
theorem Bool.beq_not_ite {a b c : Bool} :
    (a == !bif c then a else b) = (!c && (a == !b)) := by
  decide +revert

@[bv_normalize]
theorem Bool.beq_not_ite' {a b c : Bool} :
    (a == !bif c then b else a) = (c && (a == !b)) := by
  decide +revert

@[bv_normalize]
theorem Bool.not_ite_beq {a b c : Bool} :
    ((!bif c then a else b) == a) = (!c && (a == !b)) := by
  decide +revert

@[bv_normalize]
theorem Bool.not_ite_beq' {a b c : Bool} :
    ((!bif c then b else a) == a) = (c && (a == !b)) := by
  decide +revert

@[bv_normalize]
theorem BitVec.beq_not_ite {a b : BitVec (w + 1)} {c : Bool} :
    (a == ~~~bif c then a else b) = (!c && (a == ~~~b)) := by
  cases c <;> simp

@[bv_normalize]
theorem BitVec.beq_not_ite' {a b : BitVec (w + 1)} {c : Bool} :
    (a == ~~~bif c then b else a) = (c && (a == ~~~b)) := by
  cases c <;> simp

@[bv_normalize]
theorem BitVec.not_ite_beq {a b : BitVec (w + 1)} {c : Bool} :
    ((~~~bif c then a else b) == a) = (!c && (~~~b == a)) := by
  cases c <;> simp

@[bv_normalize]
theorem BitVec.not_ite_beq' {a b : BitVec (w + 1)} {c : Bool} :
    ((~~~bif c then b else a) == a) = (c && (~~~b == a)) := by
  cases c <;> simp

theorem Bool.and_left (lhs rhs : Bool) (h : (lhs && rhs) = true) : lhs = true := by
  revert lhs rhs
  decide

theorem Bool.and_right (lhs rhs : Bool) (h : (lhs && rhs) = true) : rhs = true := by
  revert lhs rhs
  decide

end Normalize
end Std.Tactic.BVDecide

