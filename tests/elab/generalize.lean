

example (x : Nat) : x + 0 = x + 0 := by
  generalize x + 0 = y
  rfl

example (x : Nat) : x + 0 = x + 0 := by
  generalize h : x + 0 = y
  rfl

example (x y w : Nat) (h : y = w) : (x + x) + w = (x + x) + y := by
  generalize h' : x + x = z
  subst y
  rfl

example (x y w : Nat) (h : x + x = y) : (x + x) + (x+x) = (x + x) + y := by
  generalize h' : x + x = z
  subst z
  subst y
  rfl

example (x y w : Nat) (h : y = w) : (x + x) + w = (x + x) + y := by
  generalize h' : x + y = z -- just add equality
  subst h
  rfl

example (x y w : Nat) (h : y = w) (H : (x + x) + w = (x + x) + y) :
    (x + x) + w = (x + x) + y := by
  generalize h' : x + x = z at H
  exact H
