open nat

inductive tree (A : Type) :=
| leaf : A → tree A
| node : tree_list A → tree A
with tree_list :=
| nil  : tree_list A
| cons : tree A → tree_list A → tree_list A

namespace tree_list

definition len {A : Type} : tree_list A → nat
| len (nil A)    := 0
| len (cons t l) := len l + 1

theorem len_nil {A : Type} : len (nil A) = 0 :=
rfl

theorem len_cons {A : Type} (t : tree A) (l : tree_list A) : len (cons t l) = len l + 1 :=
rfl

variables (A : Type) (t1 t2 t3 : tree A)

example : len (cons t1 (cons t2 (cons t3 (nil A)))) = 3 :=
rfl

print definition len

end tree_list
