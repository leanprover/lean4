inductive foo {A : Type} : A → Type :=
mk : Π a : A, foo a

example (A : Type) (B : A → Type) (a : A) (H : foo a) (Hb : B a) : A :=
begin
  cases H,
  state,
  assumption
end

inductive foo₂ {A : Type} : A → A → Type :=
mk : Π a b : A, foo₂ a b

example (A : Type) (B : A → Type) (f : A → A) (a : A) (H : foo₂ (f a) a) (Hb : H = H) (Hc : a = a) : A :=
begin
  cases H,
  state,
  exact a
end
