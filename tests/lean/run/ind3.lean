inductive tree (A : Type) : Type :=
| node : A → forest A → tree A
with forest (A : Type) : Type :=
| nil  : forest A
| cons : tree A → forest A → forest A

check tree.{1}
check forest.{1}
check tree_rec.{1 1}
check forest_rec.{1 1}

print "==============="

inductive group : Type :=
| mk_group : Π (carrier : Type) (mul : carrier → carrier → carrier) (one : carrier), group

check group.{1}
check group.{2}
check group_rec.{1 1}
