import data.examples.vector
open nat prod.ops

example (n : nat) (v₁ : vector nat n) (v₂ : vector nat 0) (h₁ : (v₂, n).2 = 0) (h₂ : n = 0) (h₃ : eq.rec_on h₁ v₁ = v₂) : v₂ = eq.rec_on h₂ v₁ :=
begin
  esimp at h₁,
  esimp at h₃,
  subst h₃
end

example (n : nat) (v₁ : vector nat n) (v₂ : vector nat 0) (h₁ : (v₂, n).2 = 0) (h₂ : n = 0) (h₃ : eq.rec_on h₁ v₁ = v₂) : v₂ = eq.rec_on h₂ v₁ :=
begin
  esimp at *,
  subst h₃
end
