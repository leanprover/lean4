open nat

inductive tree (A : Type)
| leaf : A → tree
| node : tree → tree → tree

#check tree.node

definition size {A : Type} (t : tree A) : nat :=
tree.rec (λ a, 1) (λ t₁ t₂ n₁ n₂, n₁ + n₂) t

#check _root_.size

#reduce size (tree.node (tree.node (tree.leaf 0) (tree.leaf 1))
                (tree.leaf 0))
