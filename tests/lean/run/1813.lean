open tactic

example {A B : Type} (f : A -> B) (a b c) (h1 : f a = b) (h2 : f a = c) : false :=
begin
  rw h1 at *,
  guard_hyp h1 := f a = b,
  guard_hyp h2 := b = c,
  admit
end

example {A B : Type} (f : A -> B) (a b c) (h1 : f a = b) (h2 : f a = c) : false :=
begin
  rw [id h1] at *,
  guard_hyp h1 := f a = b,
  guard_hyp h2 := b = c,
  admit
end

example {A B : Type} (f : A -> B) (a b c) (h1 : f a = b) (h2 : f a = c) : false :=
begin
  rw [id id h1] at *,
  guard_hyp h1 := f a = b,
  guard_hyp h2 := b = c,
  admit
end
