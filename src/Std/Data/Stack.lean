/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam

Simple stack API implemented using an array.
-/
namespace Std
universe u v w

structure Stack (α : Type u) where
  vals : Array α := #[]

namespace Stack

variable {α : Type u}

def empty : Stack α := {}

def isEmpty (s : Stack α) : Bool :=
  s.vals.isEmpty

def push (v : α) (s : Stack α) : Stack α :=
  { s with vals := s.vals.push v }

def peek? (s : Stack α) : Option α :=
  if s.vals.isEmpty then none else s.vals.get? (s.vals.size-1)

def peek! [Inhabited α] (s : Stack α) : α :=
  s.vals.back

def pop [Inhabited α] (s : Stack α) : Stack α :=
  { s with vals := s.vals.pop }

def modify [Inhabited α] (s : Stack α) (f : α → α) : Stack α :=
  { s with vals := s.vals.modify (s.vals.size-1) f }

end Stack
end Std
