import data.list
open list

set_option pp.implicit true

definition append : Π {A : Type}, list A → list A → list A
| append nil      l := l
| append (h :: t) l := h :: (append t l)

theorem append_nil {A : Type} (l : list A) : append nil l = l :=
rfl

theorem append_cons {A : Type} (h : A) (t l : list A) : append (h :: t) l = h :: (append t l) :=
rfl

example : append ((1:nat) :: 2 :: nil) (3 :: 4 :: 5 :: nil) = (1 :: 2 :: 3 :: 4 :: 5 :: nil) :=
rfl
