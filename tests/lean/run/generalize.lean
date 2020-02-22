new_frontend

theorem tst0 (x : Nat) : x + 0 = x + 0 :=
begin
  generalize x + 0 = y;
  exact (Eq.refl y)
end

theorem tst1 (x : Nat) : x + 0 = x + 0 :=
begin
  generalize h : x + 0 = y;
  exact (Eq.refl y)
end

theorem tst2 (x y w : Nat) (h : y = w) : (x + x) + w  = (x + x) + y :=
begin
  generalize h' : x + x = z;
  subst y;
  exact Eq.refl $ z + w
end

theorem tst3 (x y w : Nat) (h : x + x = y) : (x + x) + (x+x)  = (x + x) + y :=
begin
  generalize h' : x + x = z;
  subst z;
  subst y;
  exact rfl
end

theorem tst4 (x y w : Nat) (h : y = w) : (x + x) + w  = (x + x) + y :=
begin
  generalize h' : x + y = z; -- just add equality
  subst h;
  exact rfl
end
