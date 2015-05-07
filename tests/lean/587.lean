open quot setoid

variables A B : Type₁
variable  s : setoid A
include s
variable  f : A → B
variable  c : ∀ a₁ a₂, a₁ ≈ a₂ → f a₁ = f a₂

example (a : A) (g h : B → B) : g = h → g (quot.lift_on ⟦a⟧ f c) = h (f a) :=
begin
  intro gh,
  esimp,
  state,
  rewrite gh
end
