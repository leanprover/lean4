open nat

inductive tree (A : Type) :=
| leaf : A → tree A
| node : tree_list A → tree A
with tree_list :=
| nil  : tree_list A
| cons : tree A → tree_list A → tree_list A

namespace tree
open tree_list

definition size {A : Type} : tree A → nat
with size_l                : tree_list A → nat
| size (leaf a)     := 1
| size (node l)     := size_l l
| size_l !nil       := 0
| size_l (cons t l) := size t + size_l l

variables {A : Type}

theorem size_leaf (a : A) : size (leaf a) = 1 :=
rfl

theorem size_node (l : tree_list A) : size (node l) = size_l l :=
rfl

theorem size_l_nil : size_l (nil A) = 0 :=
rfl

theorem size_l_cons (t : tree A) (l : tree_list A) : size_l (cons t l) = size t + size_l l :=
rfl

definition eq_tree {A : Type} : tree A → tree A → Prop
with eq_tree_list             : tree_list A → tree_list A → Prop
| eq_tree (leaf a₁) (leaf a₂)            := a₁ = a₂
| eq_tree (node l₁) (node l₂)            := eq_tree_list l₁ l₂
| eq_tree _ _                            := false
| eq_tree_list !nil !nil                 := true
| eq_tree_list (cons t₁ l₁) (cons t₂ l₂) := eq_tree t₁ t₂ ∧ eq_tree_list l₁ l₂
| eq_tree_list _ _                       := false

theorem eq_tree_leaf (a₁ a₂ : A) : eq_tree (leaf a₁) (leaf a₂) = (a₁ = a₂) :=
rfl

theorem eq_tree_node (l₁ l₂ : tree_list A) : eq_tree (node l₁) (node l₂) = eq_tree_list l₁ l₂ :=
rfl

theorem eq_tree_leaf_node (a₁ : A) (l₂ : tree_list A) : eq_tree (leaf a₁) (node l₂) = false :=
rfl

theorem eq_tree_node_leaf (l₁ : tree_list A) (a₂ : A) : eq_tree (node l₁) (leaf a₂) = false :=
rfl

theorem eq_tree_list_nil : eq_tree_list (nil A) (nil A) = true :=
rfl

theorem eq_tree_list_cons (t₁ t₂ : tree A) (l₁ l₂ : tree_list A) :
  eq_tree_list (cons t₁ l₁) (cons t₂ l₂) = (eq_tree t₁ t₂ ∧ eq_tree_list l₁ l₂) :=
rfl

theorem eq_tree_list_cons_nil (t : tree A) (l : tree_list A) : eq_tree_list (cons t l) (nil A) = false :=
rfl

theorem eq_tree_list_nil_cons (t : tree A) (l : tree_list A) : eq_tree_list (nil A) (cons t l) = false :=
rfl

end tree
