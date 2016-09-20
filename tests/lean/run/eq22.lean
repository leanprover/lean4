open list

definition head {A : Type} : Π (l : list A), l ≠ nil → A
| nil h      := absurd rfl h
| (a :: l) h := a

theorem head_cons {A : Type} (a : A) (l : list A) (h : a :: l ≠ nil) : head (a :: l) h = a :=
rfl
