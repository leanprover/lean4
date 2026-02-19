/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Data.UInt.Basic
public import Init.MetaTypes

public section
namespace Lean.Meta

namespace TransparencyMode

def hash : TransparencyMode → UInt64
  | all       => 7
  | default   => 11
  | reducible => 13
  | instances => 17
  | none => 19

instance : Hashable TransparencyMode := ⟨hash⟩

def lt : TransparencyMode → TransparencyMode → Bool
  | _,         none      => false
  | none,      _         => true
  | _,         reducible => false
  | reducible, _         => true
  | _,         instances => false
  | instances, _         => true
  | default,   all       => true
  | _,         _         => false

instance : LT TransparencyMode := ⟨fun a b => a.lt b⟩
instance (a b : TransparencyMode) : Decidable (a < b) := inferInstanceAs (Decidable (a.lt b))

instance : LE TransparencyMode := ⟨fun a b => a < b ∨ a = b⟩
instance (a b : TransparencyMode) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a < b ∨ a = b))

protected def beq : TransparencyMode → TransparencyMode → Bool
  | none,      none      => true
  | reducible, reducible => true
  | instances, instances => true
  | default,   default   => true
  | all,       all       => true
  | _,         _         => false

instance : BEq TransparencyMode := ⟨TransparencyMode.beq⟩

protected def compare (a b : TransparencyMode) : Ordering :=
  if a.lt b then .lt else if b.lt a then .gt else .eq

instance : Ord TransparencyMode where
  compare := TransparencyMode.compare

end TransparencyMode

example (a b c : TransparencyMode) : a.lt b → b.lt c → a.lt c := by
  cases a <;> cases b <;> cases c <;> simp [TransparencyMode.lt]

example (a : TransparencyMode) : ¬ a.lt a := by
  cases a <;> simp [TransparencyMode.lt]

example (a b : TransparencyMode) : a.lt b → ¬ b.lt a := by
  cases a <;> cases b <;> simp [TransparencyMode.lt]

example : TransparencyMode.lt .none .reducible := rfl
example : TransparencyMode.lt .reducible .instances := rfl
example : TransparencyMode.lt .instances .default := rfl
example : TransparencyMode.lt .default .all := rfl

end Lean.Meta
