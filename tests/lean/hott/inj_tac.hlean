open nat

inductive vector (A : Type) : nat → Type :=
| nil {} : vector A zero
| cons   : Π {n}, A → vector A n → vector A (succ n)

open vector
notation a :: b := cons a b
notation `[` l:(foldr `,` (h t, cons h t) nil `]`) := l


example (a b : nat) : succ a = succ b → a + 2 = b + 2 :=
begin
  intro H,
  injection H,
  rewrite e_1
end

example (A : Type) (n : nat) (v w : vector A n) (a : A) (b : A) :
        a :: v = b :: w →  b = a :=
begin
  intro H, injection H with neqn aeqb beqw,
  rewrite aeqb
end

open prod

example (A : Type) (a₁ a₂ a₃ b₁ b₂ b₃ : A) : (a₁, a₂, a₃) = (b₁, b₂, b₃) → b₁ = a₁ :=
begin
  intro H, injection H with a₁b₁ a₂b₂ a₃b₃,
  rewrite a₁b₁
end

example (a₁ a₂ a₃ b₁ b₂ b₃ : nat) : (a₁+2, a₂+3, a₃+1) = (b₁+2, b₂+2, b₃+2) → b₁ = a₁ × a₃ = b₃+1 :=
begin
  intro H, injection H with a₁b₁ sa₂b₂ a₃sb₃,
  esimp at *,
  rewrite [a₁b₁, a₃sb₃], split,
  repeat trivial
end
