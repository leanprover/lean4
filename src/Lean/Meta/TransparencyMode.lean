/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
namespace Lean.Meta

inductive TransparencyMode where
  | all | default | reducible | instances

namespace TransparencyMode
instance : Inhabited TransparencyMode := ⟨TransparencyMode.default⟩

def beq : TransparencyMode → TransparencyMode → Bool
  | all,       all       => true
  | default,   default   => true
  | reducible, reducible => true
  | instances, instances => true
  | _,         _         => false

instance : BEq TransparencyMode := ⟨beq⟩

def hash : TransparencyMode → USize
  | all       => 7
  | default   => 11
  | reducible => 13
  | instances => 17

instance : Hashable TransparencyMode := ⟨hash⟩

def lt : TransparencyMode → TransparencyMode → Bool
  | reducible, default   => true
  | reducible, all       => true
  | reducible, instances => true
  | instances, default   => true
  | instances, all       => true
  | default,   all       => true
  | _,         _         => false

end TransparencyMode

end Lean.Meta
