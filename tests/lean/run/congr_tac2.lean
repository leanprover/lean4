import data.finset
open finset list

example (A : Type) (f : nat → nat → nat → nat) (a b : nat) : a = b → f a = f b :=
begin
  intros,
  congruence,
  assumption
end

structure finite_set [class] {T : Type} (xs : set T) :=
(to_finset : finset T) (is_equiv : to_set to_finset = xs)

definition finset_set.is_subsingleton [instance] (T : Type) (xs : set T) : subsingleton (finite_set xs) :=
begin
  constructor, intro a b,
  induction a with f₁ h₁,
  induction b with f₂ h₂,
  subst xs,
  let e := to_set.inj h₂,
  subst e
end

open finite_set

definition card {T : Type} (xs : set T) [fxs : finite_set xs] :=
finset.card (to_finset xs)

example (A : Type) (s₁ s₂ : set A) [fxs₁ : finite_set s₁] [fxs₂ : finite_set s₂] : s₁ = s₂ → card s₁ = card s₂ :=
begin
  intros,
  congruence,
  unfold set at *,
  assumption
end

example {A : Type} (l₁ l₂ : list A) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) : l₁ = l₂ → last l₁ h₁ = last l₂ h₂ :=
begin
  intros,
  congruence,
  assumption
end

example (A : Type) (last₁ last₂ : Π l : list A, l ≠ [] → A) (l₁ l₂ : list A) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
        last₁ = last₂ → l₁ = l₂ → last₁ l₁ h₁ = last₂ l₂ h₂ :=
begin
  intro e₁ e₂,
  congruence,
  repeat assumption
end
