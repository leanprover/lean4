example (A : Type) (B : A → Type) (b : B) : true :=
trivial

example : ∀ (A : Type) (B : A → Type) (b : B), true :=
begin
  intros, trivial
end

check λ (A : Type) (B : A → Type) (b : B), true

check λ (A : Type) (B : A → Type), B → true

check λ (A : Type) (B : A → Type) b, (b : B)
