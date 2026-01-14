/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Data.UInt.Basic

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
