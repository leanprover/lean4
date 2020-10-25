

theorem tst0 (x : Nat) : x + 0 = x + 0 :=
by {
  generalize x + 0 = y;
  exact (Eq.refl y)
}

theorem tst1 (x : Nat) : x + 0 = x + 0 :=
by {
  generalize h : x + 0 = y;
  exact (Eq.refl y)
}

theorem tst2 (x y w : Nat) (h : y = w) : (x + x) + w  = (x + x) + y :=
by {
  generalize h' : x + x = z;
  subst y;
  exact Eq.refl $ z + w
}

theorem tst3 (x y w : Nat) (h : x + x = y) : (x + x) + (x+x)  = (x + x) + y :=
by {
  generalize h' : x + x = z;
  subst z;
  subst y;
  exact rfl
}

theorem tst4 (x y w : Nat) (h : y = w) : (x + x) + w  = (x + x) + y :=
by {
  generalize h' : x + y = z; -- just add equality
  subst h;
  exact rfl
}
