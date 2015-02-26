import data.list
open list

definition head {A : Type} : Π (l : list A), l ≠ nil → A
| head nil h      := absurd rfl h
| head (a :: l) _ := a

theorem head_cons {A : Type} (a : A) (l : list A) (h : a :: l ≠ nil) : head (a :: l) h = a :=
rfl
