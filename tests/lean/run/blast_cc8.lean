import data.finset
open set finset

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

/- Add some instances for finite_sets -/
variable {A : Type}
definition finite_set_empty [instance] : finite_set (∅:set A) := sorry
definition finite_set_finset [instance] (fxs : finset A) : finite_set (to_set fxs) := sorry
definition finite_set_insert [instance] (xs : set A) [fxs : finite_set xs] (x : A) : finite_set (insert x xs) := sorry
definition finite_set_union [instance] (xs : set A) [fxs : finite_set xs] (ys : set A) [fys : finite_set ys] : finite_set (xs ∪ ys) := sorry
definition finite_set_inter1 [instance] (xs : set A) [fxs : finite_set xs] (ys : set A) [ys_dec : decidable_pred ys] : finite_set (xs ∩ ys) := sorry
definition finite_set_inter2 [instance] (xs : set A) [fxs : finite_set xs] (ys : set A) [ys_dec : decidable_pred ys] : finite_set (ys ∩ xs) := sorry
definition finite_set_set_of [instance] (xs : set A) [fxs : finite_set xs] : finite_set (set.set_of xs) := sorry

/- Defined cardinality using finite_set type class -/
noncomputable definition mycard {T : Type} (xs : set T) [fxs : finite_set xs] :=
finset.card (to_finset xs)

set_option blast.subst false
set_option blast.simp  false

/- Congruence closure still works :-) -/
definition tst
        (A : Type) (s₁ s₂ s₃ s₄ s₅ s₆ : set A)
        [fxs₁ : finite_set s₁] [fxs₂ : finite_set s₂]
        [fxs₁ : finite_set s₃] [fxs₂ : finite_set s₄]
        [d₁ : decidable_pred s₅] [d₂ : decidable_pred s₆] :
        s₁ = s₂ → s₃ = s₄ → s₆ = s₅ → mycard ((s₁ ∪ s₃) ∩ s₅) = mycard ((s₂ ∪ s₄) ∩ s₆) :=
by blast

print tst
