import data.sigma tools.tactic

namespace sigma
  definition no_confusion_type {A : Type} {B : A → Type} (P : Type) (v₁ v₂ : sigma B) : Type :=
  cases_on v₁
    (λ (a₁ : A) (b₁ : B a₁), cases_on v₂
      (λ (a₂ : A) (b₂ : B a₂),
         (Π (eq₁ : a₁ = a₂), eq.rec_on eq₁ b₁ = b₂ → P) → P))

  definition no_confusion {A : Type} {B : A → Type} {P : Type} {v₁ v₂ : sigma B} : v₁ = v₂ → no_confusion_type P v₁ v₂ :=
  assume H₁₂ : v₁ = v₂,
    have aux : v₁ = v₁ → no_confusion_type P v₁ v₁, from
      assume H₁₁, cases_on v₁
        (λ (a₁ : A) (b₁ : B a₁) (h : Π (eq₁ : a₁ = a₁), eq.rec_on eq₁ b₁ = b₁ → P),
           h rfl rfl),
    eq.rec_on H₁₂ aux H₁₂

 theorem sigma.mk.inj_1 {A : Type} {B : A → Type} {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} (Heq : dpair a₁ b₁ = dpair a₂ b₂) : a₁ = a₂ :=
 begin
   apply (no_confusion Heq), intros, assumption
 end

 theorem sigma.mk.inj_2 {A : Type} {B : A → Type} (a₁ a₂ : A) (b₁ : B a₁) (b₂ : B a₂) (Heq : dpair a₁ b₁ = dpair a₂ b₂) :
   eq.rec_on (sigma.mk.inj_1 Heq) b₁ = b₂ :=
 begin
   apply (no_confusion Heq), intros, eassumption
 end
end sigma
