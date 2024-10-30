/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Notation
import Init.Data.Bool

/-!
This module contains the definition of a generic boolean substructure for SMT problems with
`BoolExpr`. For verification purposes `BoolExpr.Sat` and `BoolExpr.Unsat` are provided.
-/

namespace Std.Tactic.BVDecide

inductive Gate
  | and
  | xor
  | beq
  | imp

namespace Gate

def toString : Gate → String
  | and => "&&"
  | xor => "^^"
  | beq => "=="
  | imp => "->"

def eval : Gate → Bool → Bool → Bool
  | and => (· && ·)
  | xor => (· ^^ ·)
  | beq => (· == ·)
  | imp => (· → ·)

end Gate

inductive BoolExpr (α : Type)
  | literal : α → BoolExpr α
  | const : Bool → BoolExpr α
  | not : BoolExpr α → BoolExpr α
  | gate : Gate → BoolExpr α → BoolExpr α → BoolExpr α
  | ite : BoolExpr α → BoolExpr α → BoolExpr α → BoolExpr α

namespace BoolExpr

def toString [ToString α] : BoolExpr α → String
  | literal a => ToString.toString a
  | const b => ToString.toString b
  | not x => "!" ++ toString x
  | gate g x y => "(" ++ toString x ++ " " ++ g.toString ++ " " ++ toString y ++ ")"
  | ite d l r => "(if " ++ toString d ++ " " ++ toString l ++ " " ++ toString r ++ ")"

instance [ToString α] : ToString (BoolExpr α) := ⟨toString⟩

def eval (a : α → Bool) : BoolExpr α → Bool
  | .literal l => a l
  | .const b => b
  | .not x => !eval a x
  | .gate g x y => g.eval (eval a x) (eval a y)
  | .ite d l r => if d.eval a then l.eval a else r.eval a

@[simp] theorem eval_literal : eval a (.literal l) = a l := rfl
@[simp] theorem eval_const : eval a (.const b) = b := rfl
@[simp] theorem eval_not : eval a (.not x) = !eval a x := rfl
@[simp] theorem eval_gate : eval a (.gate g x y) = g.eval (eval a x) (eval a y) := rfl
@[simp] theorem eval_ite : eval a (.ite d l r) = if d.eval a then l.eval a else r.eval a := rfl

def Sat (a : α → Bool) (x : BoolExpr α) : Prop := eval a x = true
def Unsat (x : BoolExpr α) : Prop := ∀ f, eval f x = false

theorem sat_and {x y : BoolExpr α} {a : α → Bool} (hx : Sat a x) (hy : Sat a y) :
    Sat a (BoolExpr.gate .and x y) := by
  simp only [Sat] at *
  simp [hx, hy, Gate.eval]

theorem sat_true {a : α → Bool} : Sat a (BoolExpr.const true : BoolExpr α) := rfl

end BoolExpr

end Std.Tactic.BVDecide
