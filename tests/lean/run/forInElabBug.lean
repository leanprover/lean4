import Std

namespace Std.BinomialHeapImp

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
