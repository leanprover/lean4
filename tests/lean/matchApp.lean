def f (xs ys : List α) : Nat :=
  match xs, ys with
  | [], [] => 0
  | _,  [] => 1
  | _,  _  => 2

#check fun {α : Type} (motive : List α → List α → Type)
  (h1 : Unit → motive [] [])
  (h2 : (x : List α) → motive x [])
  (h3 : (x x_1 : List α) → motive x x_1)
  => f.match_1 (motive := motive) [] [] h1 h2 h3
