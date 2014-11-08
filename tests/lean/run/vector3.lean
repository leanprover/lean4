import logic data.nat.basic
open nat

inductive vector (A : Type) : nat → Type :=
vnil  : vector A zero,
vcons : Π {n : nat}, A → vector A n → vector A (succ n)

namespace vector
  definition no_confusion {A : Type} {n : nat} {P : Type} {v₁ v₂ : vector A n} : v₁ = v₂ → no_confusion_type P v₁ v₂ :=
  assume H₁₂ : v₁ = v₂,
    have aux : v₁ = v₁ → no_confusion_type P v₁ v₁, from
      take H₁₁, cases_on v₁
        (assume h : P, h)
        (take n₁ h₁ t₁, assume h : (Π (H : n₁ = n₁), h₁ = h₁ → t₁ == t₁ → P),
          h rfl rfl !heq.refl),
    eq.rec aux H₁₂ H₁₂

  theorem vcons.inj₁ {A : Type} {n : nat} (a₁ a₂ : A) (v₁ v₂ : vector A n) : vcons a₁ v₁ = vcons a₂ v₂ → a₁ = a₂ :=
  assume h, no_confusion h (λ n h t, h)

  theorem vcons.inj₂ {A : Type} {n : nat} (a₁ a₂ : A) (v₁ v₂ : vector A n) : vcons a₁ v₁ = vcons a₂ v₂ → v₁ == v₂ :=
  assume h, no_confusion h (λ n h t, t)

end vector
