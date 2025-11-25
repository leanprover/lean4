/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Data.Repr
public section
namespace Lean.Meta.Grind
/--
Result type for satisfiability checking procedures.
-/
inductive CheckResult where
  | /-- No progress -/
    none
  | /-- Updated basis, simplified equations. -/
    progress
  | /-- Propagated equations back to the core. -/
    propagated
  | /-- Closed the goal. -/
    closed
  deriving BEq, Inhabited, Repr

def CheckResult.lt (r₁ r₂ : CheckResult) : Bool :=
  match r₁, r₂ with
  | _,          .none        => false
  | .none,       _           => true
  | _,           .progress   => false
  | .progress,   _           => true
  | _,           .propagated => false
  | .propagated, _           => true
  | .closed,     .closed     => false

def CheckResult.le (r₁ r₂ : CheckResult) : Bool :=
  r₁ == r₂ || r₁.lt r₂

/--
Joins two results. It uses the order `.none < .progress < .propagated < .closed`
-/
def CheckResult.join (r₁ r₂ : CheckResult) : CheckResult :=
  match r₁, r₂ with
  | .none,       _           => r₂
  | _,           .none       => r₁
  | .progress,   _           => r₂
  | _,           .progress   => r₁
  | .propagated, _           => r₂
  | _,           .propagated => r₁
  | .closed,     .closed     => .closed

/-! Sanity check theorems -/
section
open CheckResult
example : lt .none .progress := rfl
example : lt .progress .propagated := rfl
example : lt .propagated .closed := rfl
example {x} : lt x x = false := by cases x <;> rfl
example {x y z} : lt x y → lt y z → lt x z := by cases x <;> cases y <;> cases z <;> decide
example {x y z} : le x y → le y z → le x z := by cases x <;> cases y <;> cases z <;> decide
example {x y} : le x y ↔ x = y ∨ lt x y := by cases x <;> cases y <;> simp +decide
example {x} : le x x := by cases x <;> rfl
example {x y} : le x y → le y x → x = y := by cases x <;> cases y <;> simp +decide
example {x y} : le x (join x y) := by cases x <;> cases y <;> rfl
example {y x} : le y (join x y) := by cases x <;> cases y <;> rfl
example {x} : join x x = x := by cases x <;> rfl
end

end Lean.Meta.Grind
