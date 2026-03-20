example (a b c : Nat) (h1 : a <= b) (h2 : b <= c) : a <= c :=
  calc a
     <= b := h1
   _ <= c := h2
   _ <= c := Nat.le_refl _

example (a b c : Nat) (h1 : a <= b) (h2 : b <= c) : a <= c :=
  calc a
     <= b := h1
   _ <= c := h2

example (a b c : Nat) (h1 : a <= b) (h2 : b <= c) : a <= c :=
  calc a <= b := h1
  _ <= c := h2

example (a b c : Nat) (h1 : a <= b) (h2 : b <= c) : a <= c :=
  calc
  a <= b := h1
  _ <= c := h2

example (a b c : Nat) (h1 : a <= b) (h2 : b <= c) : a <= c :=
  calc
  a <= b := sorry
  _ <= c := h2


example (a b c : Nat) (h1 : a <= b) (h2 : b <= c) : a <= c := by
  calc a
     <= b := ?h
   _ <= c := h2
  case h => exact h1

example (a b c : Nat) (h1 : a <= b) (h2 : b <= c) : a <= c := by
  calc  a
      = a + 0 := rfl
   _ <= b := ?h
   _  = b := rfl
  case h => exact h1
  exact h2

example (a b c : Nat) (h1 : a <= b) (h2 : b <= c) : a <= c := by
  calc  _
     <= b := ?h
   _  = b := rfl
  case h => exact h1
  exact h2

example (a b c : Nat) (h1 : a <= b) (h2 : b <= c) : a <= c := by
  calc  _
     <= b := h1
   _  = b + 0 := rfl
  exact h2

example (a b c : Nat) (h1 : a <= b) (h2 : b <= c) : a <= c := by
  calc  a
     <= b := h1
   _  = b + 0 := rfl
  exact h2
