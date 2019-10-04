/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.list
import init.coe
universes u

namespace BinomialHeapImp

structure HeapNodeAux (α : Type u) (h : Type u) :=
(val : α) (rank : Nat) (children : List h)

inductive Heap (α : Type u) : Type u
| empty {} : Heap
| heap  (ns : List (HeapNodeAux α Heap)) : Heap

abbrev HeapNode (α) := HeapNodeAux α (Heap α)

variables {α : Type u}

instance : Inhabited (Heap α) := ⟨Heap.empty⟩

def hRank : List (HeapNode α) → Nat
| []   => 0
| h::_ => h.rank

def isEmpty : Heap α → Bool
| Heap.empty => true
| _          => false

def singleton (a : α) : Heap α :=
Heap.heap [{ val := a, rank := 1, children := [] }]

@[specialize] def combine (lt : α → α → Bool) (n₁ n₂ : HeapNode α) : HeapNode α :=
if lt n₂.val n₁.val then
   { rank := n₂.rank + 1, children := n₂.children ++ [Heap.heap [n₁]], .. n₂ }
else
   { rank := n₁.rank + 1, children := n₁.children ++ [Heap.heap [n₂]], .. n₁ }

@[specialize] partial def mergeNodes (lt : α → α → Bool) : List (HeapNode α) → List (HeapNode α) → List (HeapNode α)
| [], h  => h
| h,  [] => h
| f@(h₁ :: t₁), s@(h₂ :: t₂) =>
  if h₁.rank < h₂.rank then h₁ :: mergeNodes t₁ s
  else if h₂.rank < h₁.rank then h₂ :: mergeNodes t₂ f
  else
    let merged := combine lt h₁ h₂;
    let r      := merged.rank;
    if r != hRank t₁ then
      if r != hRank t₂ then merged :: mergeNodes t₁ t₂ else mergeNodes (merged :: t₁) t₂
    else
      if r != hRank t₂ then mergeNodes t₁ (merged :: t₂) else merged :: mergeNodes t₁ t₂

@[specialize] def merge (lt : α → α → Bool) : Heap α → Heap α → Heap α
| Heap.empty,    h           => h
| h,             Heap.empty  => h
| Heap.heap h₁, Heap.heap h₂ => Heap.heap (mergeNodes lt h₁ h₂)

@[specialize] def headOpt (lt : α → α → Bool) : Heap α → Option α
| Heap.empty  => none
| Heap.heap h => h.foldl
  (fun r n => match r with
   | none   => n.val
   | some v => if lt v n.val then v else n.val) none

/- O(log n) -/
@[specialize] def head [Inhabited α] (lt : α → α → Bool) : Heap α → α
| Heap.empty        => default α
| Heap.heap []      => default α
| Heap.heap (h::hs) => hs.foldl (fun r n => if lt r n.val then r else n.val) h.val

@[specialize] def findMin (lt : α → α → Bool) : List (HeapNode α) → Nat → HeapNode α × Nat → HeapNode α × Nat
| [],    _,   r          => r
| h::hs, idx, (h', idx') => if lt h.val h'.val then findMin hs (idx+1) (h, idx) else findMin hs (idx+1) (h', idx')

def tail (lt : α → α → Bool) : Heap α → Heap α
| Heap.empty        => Heap.empty
| Heap.heap []      => Heap.empty
| Heap.heap [h]     =>
  match h.children with
  | []      => Heap.empty
  | (h::hs) => hs.foldl (merge lt) h
| Heap.heap hhs@(h::hs) =>
  let (min, minIdx) := findMin lt hs 1 (h, 0);
  let rest          := hhs.eraseIdx minIdx;
  min.children.foldl (merge lt) (Heap.heap rest)

partial def toList (lt : α → α → Bool) : Heap α → List α
| Heap.empty => []
| h          => match headOpt lt h with
  | none   => []
  | some a => a :: toList (tail lt h)

inductive WellFormed (lt : α → α → Bool) : Heap α → Prop
| emptyWff                  : WellFormed Heap.empty
| singletonWff (a : α)      : WellFormed (singleton a)
| mergeWff (h₁ h₂ : Heap α) : WellFormed h₁ → WellFormed h₂ → WellFormed (merge lt h₁ h₂)
| tailWff (h : Heap α)      : WellFormed h → WellFormed (tail lt h)

end BinomialHeapImp

open BinomialHeapImp

def BinomialHeap (α : Type u) (lt : α → α → Bool) := { h : Heap α // WellFormed lt h }

@[inline] def mkBinomialHeap (α : Type u) (lt : α → α → Bool) : BinomialHeap α lt :=
⟨Heap.empty, WellFormed.emptyWff lt⟩

namespace BinomialHeap
variables {α : Type u} {lt : α → α → Bool}

@[inline] def empty : BinomialHeap α lt :=
mkBinomialHeap α lt

@[inline] def isEmpty : BinomialHeap α lt → Bool
| ⟨b, _⟩ => BinomialHeapImp.isEmpty b

/- O(1) -/
@[inline] def singleton (a : α) : BinomialHeap α lt :=
⟨BinomialHeapImp.singleton a, WellFormed.singletonWff lt a⟩

/- O(log n) -/
@[inline] def merge : BinomialHeap α lt → BinomialHeap α lt → BinomialHeap α lt
| ⟨b₁, h₁⟩, ⟨b₂, h₂⟩ => ⟨BinomialHeapImp.merge lt b₁ b₂, WellFormed.mergeWff b₁ b₂ h₁ h₂⟩

/- O(log n) -/
@[inline] def head [Inhabited α] : BinomialHeap α lt → α
| ⟨b, _⟩ => BinomialHeapImp.head lt b

/- O(log n) -/
@[inline] def headOpt : BinomialHeap α lt → Option α
| ⟨b, _⟩ => BinomialHeapImp.headOpt lt b

/- O(log n) -/
@[inline] def tail : BinomialHeap α lt → BinomialHeap α lt
| ⟨b, h⟩ => ⟨BinomialHeapImp.tail lt b, WellFormed.tailWff b h⟩

/- O(log n) -/
@[inline] def insert (a : α) (h : BinomialHeap α lt) : BinomialHeap α lt :=
merge (singleton a) h

/- O(n log n) -/
@[inline] def toList : BinomialHeap α lt → List α
| ⟨b, _⟩ => BinomialHeapImp.toList lt b

end BinomialHeap
