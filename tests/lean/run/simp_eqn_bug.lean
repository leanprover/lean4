@[simp] def f (a : Nat) (xs : List Nat) : Nat :=
  match a with
  | 25 => 0
  | _  => match xs with
   | []    => a
   | x::xs => x + f a xs

example : f 25 xs = 0 := by apply f._eq_1
example (h : a = 25 → False) : f a [] = a := by apply f._eq_2; assumption
example (h : a = 25 → False) : f a (x::xs) = x + f a xs := by apply f._eq_3; assumption
