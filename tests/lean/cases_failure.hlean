-- .hlean file
open eq

inductive square {A : Type} {a₀₀ : A}
  : Π{a₀₁ a₁₀ a₁₁ : A}, a₀₀ = a₀₁ → a₁₀ = a₁₁ → a₀₀ = a₁₀ → a₀₁ = a₁₁ → Type :=
ids : square idp idp idp idp

definition foo {A : Type} {x y z : A} {t : x = y} {b : z = y} {l : x = z} {r : y = y}
  (s : square t b l r)  : unit :=
begin
  cases s,
  exact unit.star
end
