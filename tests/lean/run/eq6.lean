open list

definition appd {A : Type} : list A → list A → list A
| nil      l := l
| (h :: t) l := h :: (appd t l)

theorem appd_nil {A : Type} (l : list A) : appd nil l = l :=
rfl

theorem appd_cons {A : Type} (h : A) (t l : list A) : appd (h :: t) l = h :: (appd t l) :=
rfl

example : appd ((1:nat) :: 2 :: nil) (3 :: 4 :: 5 :: nil) = (1 :: 2 :: 3 :: 4 :: 5 :: nil) :=
rfl
