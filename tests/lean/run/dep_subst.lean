import data.finset
open subtype setoid finset set

inductive finite_set [class] {T : Type} (xs : set T) :=
| mk : ∀ (fxs : finset T), to_set fxs = xs → finite_set xs

definition card {T : Type} (xs : set T) [fn : finite_set xs] : nat :=
begin
  induction fn,
  exact finset.card fxs
end

example {T : Type} (xs : set T) [fn₁ : finite_set xs] [fn₂ : finite_set xs] : @card T xs fn₁ = @card T xs fn₂ :=
begin
  induction fn₁ with fxs₁ h₁,
  induction fn₂ with fxs₂ h₂,
  subst xs,
  apply sorry
end

example {T : Type} (xs : set T) [fn₁ : finite_set xs] [fn₂ : finite_set xs] : @card T xs fn₁ = @card T xs fn₂ :=
begin
  induction fn₁ with fxs₁ h₁,
  induction fn₂ with fxs₂ h₂,
  subst xs,
  note aux := to_set.inj h₂,
  subst aux
end
