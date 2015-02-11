set_option pp.beta true

structure foo :=
mk :: (A : Type) (B : A → Type) (a : A) (b : B a)

namespace foo

  definition foo.inj₁
     {A₁ : Type} {B₁ : A₁ → Type} {a₁ : A₁} {b₁ : B₁ a₁}
     {A₂ : Type} {B₂ : A₂ → Type} {a₂ : A₂} {b₂ : B₂ a₂}
     (H : foo.mk A₁ B₁ a₁ b₁ = foo.mk A₂ B₂ a₂ b₂)
     : A₁ = A₂
  := lift.down (foo.no_confusion H (λ e₁ e₂ e₃ e₄, e₁))

end foo
