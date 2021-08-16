/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jannis Limperg
-/
namespace Std
universe u
namespace BinomialHeapImp

structure HeapNodeAux (α : Type u) (h : Type u) where
  val : α
  rank : Nat
  children : List h

-- A `Heap` is a forest of binomial trees.
inductive Heap (α : Type u) : Type u where
  | heap (ns : List (HeapNodeAux α (Heap α))) : Heap α
  deriving Inhabited

open Heap

-- A `HeapNode` is a binomial tree. If a `HeapNode` has rank `k`, its children
-- have ranks between `0` and `k - 1`. They are ordered by rank. Additionally,
-- the value of each child must be less than or equal to the value of its
-- parent node.
abbrev HeapNode α := HeapNodeAux α (Heap α)

variable {α : Type u}

def hRank : List (HeapNode α) → Nat
  | []   => 0
  | h::_ => h.rank

def isEmpty : Heap α → Bool
  | heap [] => true
  | _       => false

def empty : Heap α :=
  heap []

def singleton (a : α) : Heap α :=
  heap [{ val := a, rank := 1, children := [] }]

-- Combine two binomial trees of rank `r`, creating a binomial tree of rank
-- `r + 1`.
@[specialize] def combine (le : α → α → Bool) (n₁ n₂ : HeapNode α) : HeapNode α :=
  if le n₂.val n₁.val then
     { n₂ with rank := n₂.rank + 1, children := n₂.children ++ [heap [n₁]] }
  else
     { n₁ with rank := n₁.rank + 1, children := n₁.children ++ [heap [n₂]] }

-- Merge two forests of binomial trees. The forests are assumed to be ordered
-- by rank and `mergeNodes` maintains this invariant.
@[specialize] partial def mergeNodes (le : α → α → Bool) : List (HeapNode α) → List (HeapNode α) → List (HeapNode α)
  | [], h  => h
  | h,  [] => h
  | f@(h₁ :: t₁), s@(h₂ :: t₂) =>
    if h₁.rank < h₂.rank then h₁ :: mergeNodes le t₁ s
    else if h₂.rank < h₁.rank then h₂ :: mergeNodes le t₂ f
    else
      let merged := combine le h₁ h₂
      let r      := merged.rank
      if r != hRank t₁ then
        if r != hRank t₂ then merged :: mergeNodes le t₁ t₂ else mergeNodes le (merged :: t₁) t₂
      else
        if r != hRank t₂ then mergeNodes le t₁ (merged :: t₂) else merged :: mergeNodes le t₁ t₂

@[specialize] def merge (le : α → α → Bool) : Heap α → Heap α → Heap α
  | heap h₁, heap h₂ => heap (mergeNodes le h₁ h₂)

@[specialize] def head? (le : α → α → Bool) : Heap α → Option α
  | heap []      => none
  | heap (h::hs) => some $
    hs.foldl (init := h.val) fun r n => if le r n.val then r else n.val

@[inline] def head [Inhabited α] (le : α → α → Bool) (h : Heap α) : α :=
  head? le h |>.getD arbitrary

@[specialize] def findMin (le : α → α → Bool) : List (HeapNode α) → Nat → HeapNode α × Nat → HeapNode α × Nat
  | [],    _,   r          => r
  | h::hs, idx, (h', idx') => if le h'.val h.val then findMin le hs (idx+1) (h', idx') else findMin le hs (idx+1) (h, idx)
    -- It is important that we check `le h'.val h.val` here, not the other way
    -- around. This ensures that head? and findMin find the same element even
    -- when we have `le h'.val h.val` and `le h.val h'.val` (i.e. le is not
    -- irreflexive).

def deleteMin (le : α → α → Bool) : Heap α → Option (α × Heap α)
  | heap [] => none
  | heap [h] =>
    let tail :=
      match h.children with
      | [] => empty
      | (h::hs) => hs.foldl (merge le) h
    some (h.val, tail)
  | heap hhs@(h::hs) =>
    let (min, minIdx) := findMin le hs 1 (h, 0)
    let rest          := hhs.eraseIdx minIdx
    let tail          := min.children.foldl (merge le) (heap rest)
    some (min.val, tail)

@[inline] def tail? (le : α → α → Bool) (h : Heap α) : Option (Heap α) :=
  deleteMin le h |>.map (·.snd)

@[inline] def tail (le : α → α → Bool) (h : Heap α) : Heap α :=
  tail? le h |>.getD empty

partial def toList (le : α → α → Bool) (h : Heap α) : List α :=
  match deleteMin le h with
  | none          => []
  | some (hd, tl) => hd :: toList le tl

partial def toArray (le : α → α → Bool) (h : Heap α) : Array α :=
  go #[] h
  where
    go (acc : Array α) (h : Heap α) : Array α :=
      match deleteMin le h with
      | none => acc
      | some (hd, tl) => go (acc.push hd) tl

partial def toListUnordered : Heap α → List α
  | heap ns => ns.bind fun n => n.val :: n.children.bind toListUnordered

partial def toArrayUnordered (h : Heap α) : Array α :=
  go #[] h
  where
    go (acc : Array α) : Heap α → Array α
      | heap ns => do
        let mut acc := acc
        for n in ns do
          acc := acc.push n.val
          for h in n.children do
            acc := go acc h
        return acc

inductive WellFormed (le : α → α → Bool) : Heap α → Prop where
  | empty                : WellFormed le empty
  | singleton (a)        : WellFormed le (singleton a)
  | merge (h₁ h₂)        : WellFormed le h₁ → WellFormed le h₂ → WellFormed le (merge le h₁ h₂)
  | deleteMin (a) (h tl) : WellFormed le h → deleteMin le h = some (a, tl) → WellFormed le tl

theorem WellFormed.tail? {le} (h tl : Heap α) (hwf : WellFormed le h) (eq : tail? le h = some tl) : WellFormed le tl := by
  simp only [BinomialHeapImp.tail?] at eq
  match eq₂: BinomialHeapImp.deleteMin le h with
    | none =>
      rw [eq₂] at eq; cases eq
    | some (a, tl) =>
      rw [eq₂] at eq; cases eq
      exact deleteMin _ _ _ hwf eq₂

theorem WellFormed.tail {le} (h : Heap α) (hwf : WellFormed le h) : WellFormed le (tail le h) := by
  simp only [BinomialHeapImp.tail]
  match eq: BinomialHeapImp.tail? le h with
    | none => exact empty
    | some tl => exact tail? _ _ hwf eq

end BinomialHeapImp

open BinomialHeapImp

def BinomialHeap (α : Type u) (le : α → α → Bool) := { h : Heap α // WellFormed le h }

@[inline] def mkBinomialHeap (α : Type u) (le : α → α → Bool) : BinomialHeap α le :=
  ⟨empty, WellFormed.empty⟩

namespace BinomialHeap
variable {α : Type u} {le : α → α → Bool}

@[inline] def empty : BinomialHeap α le :=
  mkBinomialHeap α le

@[inline] def isEmpty : BinomialHeap α le → Bool
  | ⟨b, _⟩ => BinomialHeapImp.isEmpty b

/- O(1) -/
@[inline] def singleton (a : α) : BinomialHeap α le :=
  ⟨BinomialHeapImp.singleton a, WellFormed.singleton a⟩

/- O(log n) -/
@[inline] def merge : BinomialHeap α le → BinomialHeap α le → BinomialHeap α le
  | ⟨b₁, h₁⟩, ⟨b₂, h₂⟩ => ⟨BinomialHeapImp.merge le b₁ b₂, WellFormed.merge b₁ b₂ h₁ h₂⟩

/- O(log n) -/
@[inline] def insert (a : α) (h : BinomialHeap α le) : BinomialHeap α le :=
  merge (singleton a) h

/- O(n log n) -/
def ofList (le : α → α → Bool) (as : List α) : BinomialHeap α le :=
  as.foldl (flip insert) empty

/- O(n log n) -/
def ofArray (le : α → α → Bool) (as : Array α) : BinomialHeap α le :=
  as.foldl (flip insert) empty

/- O(log n) -/
@[inline] def deleteMin : BinomialHeap α le → Option (α × BinomialHeap α le)
  | ⟨b, h⟩ =>
    match eq: BinomialHeapImp.deleteMin le b with
    | none => none
    | some (a, tl) => some (a, ⟨tl, WellFormed.deleteMin a b tl h eq⟩)

/- O(log n) -/
@[inline] def head [Inhabited α] : BinomialHeap α le → α
  | ⟨b, _⟩ => BinomialHeapImp.head le b

/- O(log n) -/
@[inline] def head? : BinomialHeap α le → Option α
  | ⟨b, _⟩ => BinomialHeapImp.head? le b

/- O(log n) -/
@[inline] def tail? : BinomialHeap α le → Option (BinomialHeap α le)
  | ⟨b, h⟩ =>
    match eq: BinomialHeapImp.tail? le b with
    | none => none
    | some tl => some ⟨tl, WellFormed.tail? b tl h eq⟩

/- O(log n) -/
@[inline] def tail : BinomialHeap α le → BinomialHeap α le
  | ⟨b, h⟩ => ⟨BinomialHeapImp.tail le b, WellFormed.tail b h⟩

/- O(n log n) -/
@[inline] def toList : BinomialHeap α le → List α
  | ⟨b, _⟩ => BinomialHeapImp.toList le b

/- O(n log n) -/
@[inline] def toArray : BinomialHeap α le → Array α
  | ⟨b, _⟩ => BinomialHeapImp.toArray le b

/- O(n) -/
@[inline] def toListUnordered : BinomialHeap α le → List α
  | ⟨b, _⟩ => BinomialHeapImp.toListUnordered b

/- O(n) -/
@[inline] def toArrayUnordered : BinomialHeap α le → Array α
  | ⟨b, _⟩ => BinomialHeapImp.toArrayUnordered b

end BinomialHeap
end Std
