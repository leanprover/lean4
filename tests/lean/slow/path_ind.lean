import hott

open path
set_option pp.beta true

variables {A : Type} {B : A → Type} {C : Π a : A, B a → Type} {D : Π (a : A) (b : B a), C a b → Type}

structure foo :=
mk :: (a : A) (b : B a) (c : C a b)

set_option unifier.max_steps 50000

definition foo.eq {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} {c₁ : C a₁ b₁} {c₂ : C a₂ b₂}
                  (H₁ : a₁ ≈ a₂)
                  (H₂ : path.rec_on H₁ b₁ ≈ b₂)
                  (H₃ : path.rec_on H₂ (path.rec_on H₁ c₁) ≈ c₂)
                  : foo.mk a₁ b₁ c₁ ≈ foo.mk a₂ b₂ c₂ :=
have aux₁: Π (b₂ : B a₁) (c₂ : C a₁ b₂)
             (H₂ : path.rec_on idp b₁ ≈ b₂)
             (H₃ : path.rec_on H₂ (path.rec_on idp c₁) ≈ c₂),
             foo.mk a₁ b₁ c₁ ≈ foo.mk a₁ b₂ c₂, from
  λ (b₂ : B a₁) (c₂ : C a₁ b₂)
    (H₂ : b₁ ≈ b₂) (H₃ : path.rec_on H₂ c₁ ≈ c₂),
    have aux₂ : Π (c₂ : C a₁ b₁) (H₃ : path.rec_on idp c₁ ≈ c₂),
               foo.mk a₁ b₁ c₁ ≈ foo.mk a₁ b₁ c₂, from
      λ (c₂ : C a₁ b₁) (H₃ : c₁ ≈ c₂),
        have aux₃ : foo.mk a₁ b₁ c₁ ≈ foo.mk a₁ b₁ c₁, from
          idp,
        path.rec_on H₃ aux₃,
    path.rec_on H₂ aux₂ c₂ H₃,
path.rec_on H₁ aux₁ b₂ c₂ H₂ H₃
