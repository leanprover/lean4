def Div : nat → nat → nat
| x y :=
  if h : 0 < y ∧ y ≤ x then
     have x - y < x, from nat.sub_lt (nat.lt_of_lt_of_le h.left h.right) h.left,
     Div (x - y) y + 1
  else
     0
