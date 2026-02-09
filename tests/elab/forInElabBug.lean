structure HeapNodeAux (α : Type u) (h : Type u) where
  val : α
  children : List h

-- A `Heap` is a forest of binomial trees.
inductive Heap (α : Type u) : Type u where
  | heap (ns : List (HeapNodeAux α (Heap α))) : Heap α
  deriving Inhabited

open Heap

partial def toArrayUnordered' (h : Heap α) : Array α :=
  go #[] h
where
  go (acc : Array α) : Heap α → Array α
    | heap ns => Id.run do
      let mut acc := acc
      for h₁ : n in ns do
        acc := acc.push n.val
        for h₂ : h in n.children do
          acc := go acc h
      return acc
