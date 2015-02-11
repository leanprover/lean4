import data.sigma

namespace sigma
  namespace manual
  definition no_confusion_type {A : Type} {B : A → Type} (P : Type) (v₁ v₂ : sigma B) : Type :=
  sigma.rec_on v₁
    (λ (a₁ : A) (b₁ : B a₁), sigma.rec_on v₂
      (λ (a₂ : A) (b₂ : B a₂),
         (Π (eq₁ : a₁ = a₂), eq.rec_on eq₁ b₁ = b₂ → P) → P))

  definition no_confusion {A : Type} {B : A → Type} {P : Type} {v₁ v₂ : sigma B} : v₁ = v₂ → no_confusion_type P v₁ v₂ :=
  assume H₁₂ : v₁ = v₂,
    have aux : v₁ = v₁ → no_confusion_type P v₁ v₁, from
      assume H₁₁, sigma.rec_on v₁
        (λ (a₁ : A) (b₁ : B a₁) (h : Π (eq₁ : a₁ = a₁), eq.rec_on eq₁ b₁ = b₁ → P),
           h rfl rfl),
    eq.rec_on H₁₂ aux H₁₂
 end manual

 theorem sigma.mk.inj_1 {A : Type} {B : A → Type} {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} (Heq : mk a₁ b₁ = mk a₂ b₂) : a₁ = a₂ :=
 begin
   apply (sigma.no_confusion Heq), intros, assumption
 end

 theorem sigma.mk.inj_2 {A : Type} {B : A → Type} (a₁ a₂ : A) (b₁ : B a₁) (b₂ : B a₂) (Heq : mk a₁ b₁ = mk a₂ b₂) : b₁ == b₂ :=
 begin
   apply (sigma.no_confusion Heq), intros, eassumption
 end
end sigma
