open list

variable {A : Type}
set_option pp.implicit true

definition app : list A → list A → list A
| nil      l := l
| (h :: t) l := h :: (app t l)

theorem app_nil (l : list A) : app nil l = l :=
rfl

theorem app_cons (h : A) (t l : list A) : app (h :: t) l = h :: (app t l) :=
rfl

example : app ((1:nat) :: 2 :: nil) (3 :: 4 :: 5 :: nil) = (1 :: 2 :: 3 :: 4 :: 5 :: nil) :=
rfl
