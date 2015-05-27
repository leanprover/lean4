set_option pp.universes true
check @not

inductive list (A : Type) : Type :=
| nil {} : list A
| cons   : A → list A → list A

namespace list
  open lift

  theorem nil_ne_cons {A : Type} (a : A) (v : list A) : nil ≠ cons a v :=
  λ H, down (list.no_confusion H)

  theorem cons.inj₁ {A : Type} (a₁ a₂ : A) (v₁ v₂ : list A) : cons a₁ v₁ = cons a₂ v₂ → a₁ = a₂ :=
  λ H, down (list.no_confusion H (λ (h₁ : a₁ = a₂) (h₂ : v₁ = v₂), h₁))

  theorem cons.inj₂ {A : Type} (a₁ a₂ : A) (v₁ v₂ : list A) : cons a₁ v₁ = cons a₂ v₂ → v₁ = v₂ :=
  λ H, down (list.no_confusion H (λ (h₁ : a₁ = a₂) (h₂ : v₁ = v₂), h₂))

end list
