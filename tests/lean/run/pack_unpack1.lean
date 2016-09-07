set_option new_elaborator true

inductive tree_core (A : Type) : bool → Type
| leaf'    : A → tree_core ff
| node'    : tree_core tt → tree_core ff
| nil' {}  : tree_core tt
| cons'    : tree_core ff → tree_core tt → tree_core tt

attribute [reducible]
definition tree (A : Type) := tree_core A ff

attribute [reducible]
definition tree_list (A : Type) := tree_core A tt

open tree_core

definition pack {A : Type} : list (tree A) → tree_core A tt
| []     := nil'
| (a::l) := cons' a (pack l)

definition unpack {A : Type} : ∀ {b}, tree_core A b → list (tree A)
| .tt nil'         := []
| .tt (cons' a t)  := a :: unpack t
| .ff (leaf' a)    := []
| .ff (node' l)    := []

attribute [inverse]
lemma unpack_pack {A : Type} : ∀ (l : list (tree A)), unpack (pack l) = l
| []     := rfl
| (a::l) :=
  show a :: unpack (pack l) = a :: l, from
  congr_arg (λ x, a :: x) (unpack_pack l)

attribute [pattern]
definition tree.node {A : Type} (l : list (tree A)) : tree A :=
tree_core.node' (pack l)

attribute [pattern]
definition tree.leaf {A : Type} : A → tree A :=
tree_core.leaf'

definition sz {A : Type} : tree A → nat
| (tree.leaf a) := 0
| (tree.node l) := list.length l

open tree

print sz

example : sz (node [leaf tt, leaf tt, leaf ff]) = 3 :=
rfl
