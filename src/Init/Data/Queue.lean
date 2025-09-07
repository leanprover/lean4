/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam

Simple queue implemented using two lists.
Note: this is only a temporary placeholder.
-/
module

prelude
public import Init.Data.List.Control

public section

namespace Std

/--
A functional queue data structure, using two back-to-back lists.
If we think of the queue as having elements pushed on the front and
popped from the back, then the queue itself is effectively `eList ++ dList.reverse`.
-/
structure Queue (α : Type u) where
  /-- The enqueue list, which stores elements that have just been pushed
  (with the most recently enqueued elements at the head). -/
  eList : List α := []
  /-- The dequeue list, which buffers elements ready to be dequeued
  (with the head being the next item to be yielded by `dequeue?`). -/
  dList : List α := []

namespace Queue

variable {α : Type u}

/-- `O(1)`. The empty queue. -/
def empty : Queue α := {}

instance : EmptyCollection (Queue α) := ⟨.empty⟩
instance : Inhabited (Queue α) := ⟨∅⟩

/-- `O(1)`. Is the queue empty? -/
def isEmpty (q : Queue α) : Bool :=
  q.dList.isEmpty && q.eList.isEmpty

/-- `O(1)`. Push an element on the front of the queue. -/
def enqueue (v : α) (q : Queue α) : Queue α :=
  { q with eList := v::q.eList }

/-- `O(|vs|)`. Push a list of elements `vs` on the front of the queue. -/
def enqueueAll (vs : List α) (q : Queue α) : Queue α :=
  { q with eList := vs ++ q.eList }

/--
`O(1)` amortized, `O(n)` worst case. Pop an element from the back of the queue,
returning the element and the new queue.
-/
def dequeue? (q : Queue α) : Option (α × Queue α) :=
  match q.dList with
  | d::ds => some (d, { q with dList := ds })
  | []    =>
    match q.eList.reverse with
    | []    => none
    | d::ds => some (d, { eList := [], dList := ds })

def toArray (q : Queue α) : Array α :=
  q.dList.toArray ++ q.eList.toArray.reverse

/--
`O(n)`. Applies the monadic predicate `p` to every element in the queue, and returns the queue
of elements for which `p` returns `true`. Note that there are currently no guarantees for the order
that `p` is applied in.
-/
@[specialize]
def filterM {m : Type → Type v} [Monad m] {α : Type} (p : α → m Bool) (q : Queue α) :
    m (Queue α) := do
  let dList ← q.dList.filterM p
  let eList ← q.eList.filterM p
  if dList.isEmpty then
    return { dList := eList.reverse, eList := [] }
  else
    return { dList, eList }
