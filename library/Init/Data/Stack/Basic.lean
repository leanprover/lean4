/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam

Simple stack API implemented using an array.
-/
prelude
import Init.Data.Array
import Init.Data.Int
universes u v w

structure Stack (α : Type u) :=
(vals : Array α := Array.empty)

namespace Stack

variable {α : Type u}

def empty : Stack α :=
{ vals := Array.empty }

def isEmpty (s : Stack α) : Bool :=
s.vals.isEmpty

def push (v : α) (s : Stack α) : Stack α :=
{ vals := s.vals.push v .. s }

def peek? (s : Stack α) : Option α :=
if s.vals.isEmpty then none else s.vals.get? (s.vals.size-1)

def peek! [Inhabited α] (s : Stack α) : α :=
s.vals.back

def pop [Inhabited α] (s : Stack α) : Stack α :=
{ vals := s.vals.pop .. s }

def modify [Inhabited α] (s : Stack α) (f : α → α) : Stack α :=
{ vals := s.vals.modify (s.vals.size-1) f .. s }

end Stack
