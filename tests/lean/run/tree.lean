import logic
open eq.ops

inductive tree (A : Type) :=
leaf : A → tree A,
node : tree A → tree A → tree A

namespace tree
  definition cases_on {A : Type} {C : tree A → Type} (t : tree A) (e₁ : Πa, C (leaf a)) (e₂ : Πt₁ t₂, C (node t₁ t₂)) : C t :=
  rec e₁ (λt₁ t₂ r₁ r₂, e₂ t₁ t₂) t


  definition no_confusion_type {A : Type} (P : Type) (t₁ t₂ : tree A) : Type :=
  cases_on t₁
   (λ a₁, cases_on t₂
     (λ a₂,    (a₁ = a₂ → P) → P)
     (λ l₂ r₂, P))
   (λ l₁ r₁, cases_on t₂
     (λ a₂,    P)
     (λ l₂ r₂, (l₁ = l₂ → r₁ = r₂ → P) → P))

  set_option pp.universes true
  check no_confusion_type

  definition no_confusion {A : Type} (P : Type) (t₁ t₂ : tree A) : t₁ = t₂ → no_confusion_type P t₁ t₂ :=
  assume e₁ : t₁ = t₂,
    have aux₁ : t₁ = t₁ → no_confusion_type P t₁ t₁, from
      take h, cases_on t₁
        (λ a,   assume h : a = a → P, h (eq.refl a))
        (λ l r, assume h : l = l → r = r → P, h (eq.refl l) (eq.refl r)),
    eq.rec aux₁ e₁ e₁

  check no_confusion

  theorem leaf_ne_tree {A : Type} (a : A) (l r : tree A) : leaf a ≠ node l r :=
  assume h : leaf a = node l r,
  no_confusion false (leaf a) (node l r) h
end tree
