/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/

namespace Lean

inductive Occurrences where
  | all
  | pos (idxs : List Nat)
  | neg (idxs : List Nat)

namespace Occurrences

instance : Inhabited Occurrences := ⟨all⟩

def contains : Occurrences → Nat → Bool
  | all,      _   => true
  | pos idxs, idx => idxs.contains idx
  | neg idxs, idx => !idxs.contains idx

def isAll : Occurrences → Bool
  | all => true
  | _   => false

def beq : Occurrences → Occurrences → Bool
  | all,     all     => true
  | pos is₁, pos is₂ => is₁ == is₂
  | neg is₁, neg is₂ => is₁ == is₂
  | _,       _       => false

instance : BEq Occurrences := ⟨beq⟩

end Occurrences

end Lean
