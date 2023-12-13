/-
The derive handlers should manage both inductives and not ignore the second one,
Fixes `#3057`
-/

mutual
  inductive Tree : Type :=
    | node : ListTree → Tree
    deriving Repr, DecidableEq, BEq, Hashable, Ord

  inductive ListTree : Type :=
    | nil : ListTree
    | cons : Tree → ListTree → ListTree
    deriving Repr, DecidableEq, BEq, Hashable, Ord
end

#synth Repr Tree
#synth Repr ListTree
#synth DecidableEq Tree
#synth DecidableEq ListTree
#synth BEq Tree
#synth BEq ListTree
#synth Hashable Tree
#synth Hashable ListTree
#synth Ord Tree
#synth Ord ListTree
