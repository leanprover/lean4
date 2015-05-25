inductive list (A : Type) :=
| nil  : list A
| cons : A → list A → list A

open nat prod

example (A B : Type) (d c : nat) (h₀ : c = 0) (a : A) (b : list B) (h₁ : A = list B) (h₂ : eq.rec_on h₁ a = @list.nil B) (h₃ : d = c) (h₄ : d + 1 = d + 2)
        : b = eq.rec_on h₁ a × c = 1:=
begin
  substvars,
  state,
  injection h₄,
  contradiction
end
