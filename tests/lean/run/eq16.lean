import data.list
open list

variable {A : Type}
set_option pp.implicit true

definition append : list A → list A → list A
| append nil      l := l
| append (h :: t) l := h :: (append t l)

theorem append_nil (l : list A) : append nil l = l :=
rfl

theorem append_cons (h : A) (t l : list A) : append (h :: t) l = h :: (append t l) :=
rfl

example : append ((1:num) :: 2 :: nil) (3 :: 4 :: 5 :: nil) = (1 :: 2 :: 3 :: 4 :: 5 :: nil) :=
rfl
