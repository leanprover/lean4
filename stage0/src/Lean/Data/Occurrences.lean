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
  deriving Inhabited, BEq

def Occurrences.contains : Occurrences → Nat → Bool
  | all,      _   => true
  | pos idxs, idx => idxs.contains idx
  | neg idxs, idx => !idxs.contains idx

def Occurrences.isAll : Occurrences → Bool
  | all => true
  | _   => false

end Lean
