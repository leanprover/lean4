theorem test1 {α} (a b : α) (as bs : List α) (h : a::as = b::bs) : a = b :=
by {
  injection h
}

theorem test2 {α} (a b : α) (f : α → α) (as bs : List α) (h : a::as = b::bs) : f a = f b :=
by {
  injection h with h1 h2;
  rw [h1]
}

theorem test3 {α} (a b : α) (f : List α → List α) (as bs : List α) (h : (x : List α) → (y : List α) → x = y) : f as = f bs :=
have : a::as = b::bs := h (a::as) (b::bs);
by {
  injection this with h1 h2;
  rw [h2]
}

theorem test4 {α} (a b : α) (f : List α → List α) (as bs : List α) (h : (x : List α) → (y : List α) → x = y) : f as = f bs :=
by {
  injection h (a::as) (b::bs) with h1 h2;
  rw [h2]
}

theorem test5 {α} (a : α) (as : List α) (h : a::as = []) : 0 > 1 :=
by {
  injection h
}

theorem test6 (n : Nat) (h : n+1 = 0) : 0 > 1 :=
by {
  injection h
}

theorem test7 (n m k : Nat) (h : n + 1 = m + 1) : m = k → n = k :=
by {
  injection h with h₁;
  subst h₁;
  intro h₂;
  exact h₂
}
