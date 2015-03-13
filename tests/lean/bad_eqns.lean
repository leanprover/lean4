open nat

definition foo1 : nat → nat
| foo1 (0 + x) := x

definition foo2 : nat → nat → nat
| foo2 0 _   := 0
| foo2 x ⌞y⌟ := x

definition foo3 : nat → nat → nat
| foo3 0   _ := 0
| foo3 ⌞x⌟ x := x

inductive tree (A : Type) :=
| node   : tree_list A → tree A
| leaf   : A → tree A
with tree_list :=
| nil {} : tree_list A
| cons   : tree A → tree_list A → tree_list A

definition is_leaf {A : Type} : tree A → bool
with is_leaf_aux : tree_list A → bool
| is_leaf (tree.node _)            := bool.ff
| is_leaf (tree.leaf _)            := bool.tt
| is_leaf_aux tree_list.nil        := bool.ff
| is_leaf_aux (tree_list.cons _ _) := bool.ff

definition foo : nat → nat
| foo 0     := 0
| foo (x+1) := let y := x + 2 in y * y

example : foo 5 = 36 := rfl

definition boo : nat → nat
| boo (x + 1) := boo (x + 2)
| boo 0       := 0
