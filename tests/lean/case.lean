example (xs : list ℕ) : ℕ :=
begin
  induction xs,
  case list.cons {}
end

example (xs : list ℕ) : ℕ :=
begin
  cases xs,
  case list.cons {}
end

example (xs : list ℕ) : ℕ :=
begin
  induction xs,
  case list.cons : x xs {
    cases xs,
    case list.cons : x xs {}
  }
end

open list
example (xs : list ℕ) : ℕ :=
begin
  induction xs,
  case cons {}
end

example (xs : list ℕ) : ℕ :=
begin
  induction xs,
  case list.cons : x xs ih { apply ih },
  case list.nil { apply 0 }
end
