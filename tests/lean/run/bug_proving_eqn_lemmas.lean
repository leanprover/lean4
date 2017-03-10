universe variables u

inductive bintree (α : Type u)
| leaf : α → bintree
| node : bintree → bintree → bintree

open bintree

def to_list {α : Type u} : bintree α → list α → list α
| (leaf α) l     := α :: l
| (node t₁ t₂) l := to_list t₁ (to_list t₂ l)

#eval to_list (node (node (leaf 1) (leaf 2)) (node (leaf 3) (leaf 4))) []
