inductive tree.{u} (A : Type.{u}) : Type.{max u 1} :=
| node : A → forest.{u} A → tree.{u} A
with forest.{u} (A : Type.{u}) : Type.{max u 1} :=
| nil  : forest.{u} A
| cons : tree.{u} A → forest.{u} A → forest.{u} A

check tree.{1}
check forest.{1}
check tree_rec.{1 1}
check forest_rec.{1 1}
