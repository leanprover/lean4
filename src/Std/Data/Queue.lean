/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam

Simple queue implemented using two lists.
Note: this is only a temporary placeholder.
-/
namespace Std
universe u v w

structure Queue (α : Type u) where
  eList : List α := []
  dList : List α := []

namespace Queue

variable {α : Type u}

def empty : Queue α :=
  { eList := [], dList := [] }

def isEmpty (q : Queue α) : Bool :=
  q.dList.isEmpty && q.eList.isEmpty

def enqueue (v : α) (q : Queue α) : Queue α :=
  { q with eList := v::q.eList }

def enqueueAll (vs : List α) (q : Queue α) : Queue α :=
  { q with eList := vs ++ q.eList }

def dequeue? (q : Queue α) : Option (α × Queue α) :=
  match q.dList with
  | d::ds => some (d, { q with dList := ds })
  | []    =>
    match q.eList.reverse with
    | []    => none
    | d::ds => some (d, { eList := [], dList := ds })

end Queue
end Std
