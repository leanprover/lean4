new_frontend

theorem test1 {α} (a b : α) (as bs : List α) (h : a::as = b::bs) : a = b :=
begin
  injection h;
  assumption;
end

theorem test2 {α} (a b : α) (as bs : List α) (h : a::as = b::bs) : a = b :=
begin
  injection h with h1 h2;
  exact h1
end

theorem test3 {α} (a b : α) (as bs : List α) (h : (x : List α) → (y : List α) → x = y) : as = bs :=
have a::as = b::bs from h (a::as) (b::bs);
begin
  injection this with h1 h2;
  exact h2
end

theorem test4 {α} (a b : α) (as bs : List α) (h : (x : List α) → (y : List α) → x = y) : as = bs :=
begin
  injection h (a::as) (b::bs) with h1 h2;
  exact h2
end

theorem test5 {α} (a : α) (as : List α) (h : a::as = []) : 0 > 1 :=
begin
  injection h
end

theorem test6 (n : Nat) (h : n+1 = 0) : 0 > 1 :=
begin
  injection h
end
