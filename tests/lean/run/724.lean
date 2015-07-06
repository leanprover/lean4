import data.list

open list bool nat
definition filter {A} : list A → (A → bool) → list A
| filter [] p := []
| filter (a :: l) p :=
  match p a with
  | tt := a :: filter l p
  | ff := filter l p
  end

example : list ℕ := filter [0, 3, 7, 2, 4, 6, 3, 4]
    (λ(n : ℕ), begin induction n, exact tt, induction v_0, exact tt, exact ff end)

definition foo  : list ℕ := filter [0, 3, 7, 2, 4, 6, 3, 4]
    (λ(n : ℕ), begin induction n, exact tt, induction v_0, exact tt, exact ff end)

example : foo = [0, 2, 4, 6, 4] := rfl
