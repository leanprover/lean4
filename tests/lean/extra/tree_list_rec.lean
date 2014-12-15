open nat

inductive tree (A : Type) :=
leaf : A → tree A,
node : tree_list A → tree A
with tree_list :=
nil  : tree_list A,
cons : tree A → tree_list A → tree_list A

namespace tree
open tree_list

definition size {A : Type} : tree A → nat
with size_l                : tree_list A → nat,
size (leaf a)     := 1,
size (node l)     := size_l l,
size_l !nil       := 0,
size_l (cons t l) := size t + size_l l

definition eq_tree {A : Type} : tree A → tree A → Prop
with eq_tree_list             : tree_list A → tree_list A → Prop,
eq_tree (leaf a₁) (leaf a₂)            := a₁ = a₂,
eq_tree (node l₁) (node l₂)            := eq_tree_list l₁ l₂,
eq_tree _ _                            := false,
eq_tree_list !nil !nil                 := true,
eq_tree_list (cons t₁ l₁) (cons t₂ l₂) := eq_tree t₁ t₂ ∧ eq_tree_list l₁ l₂,
eq_tree_list _ _                       := false

end tree
