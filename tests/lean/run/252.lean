open nat

inductive tree (A : Type) :=
leaf : A → tree A,
node : tree A → tree A → tree A

check tree.node

definition size {A : Type} (t : tree A) : nat :=
tree.rec (λ a, 1) (λ t₁ t₂ n₁ n₂, n₁ + n₂) t

check size

eval size (tree.node (tree.node (tree.leaf 0) (tree.leaf 1))
                (tree.leaf 0))
