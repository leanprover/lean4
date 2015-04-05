open nat

definition id [unfold-f] {A : Type} (a : A) := a
definition compose {A B C : Type} (g : B → C) (f : A → B) (a : A) := g (f a)
notation g ∘ f := compose g f

example (a b : nat) (H : a = b) : id a = b :=
begin
  esimp,
  state,
  exact H
end

example (a b : nat) (H : a = b) : (id ∘ id) a = b :=
begin
  esimp,
  state,
  exact H
end

attribute compose [unfold-f]

example (a b : nat) (H : a = b) : (id ∘ id) a = b :=
begin
  esimp,
  state,
  exact H
end
