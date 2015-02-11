namespace sigma
  open lift
  open sigma.ops sigma
  variables {A : Type} {B : A → Type}

  variables {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}

  definition dpair.inj (H : ⟨a₁, b₁⟩ = ⟨a₂, b₂⟩) : Σ (e₁ : a₁ = a₂), eq.rec b₁ e₁ = b₂ :=
  down (sigma.no_confusion H (λ e₁ e₂, ⟨e₁, e₂⟩))

  definition dpair.inj₁ (H : ⟨a₁, b₁⟩ = ⟨a₂, b₂⟩) : a₁ = a₂ :=
  (dpair.inj H).1

  definition dpair.inj₂ (H : ⟨a₁, b₁⟩ = ⟨a₂, b₂⟩) : eq.rec b₁ (dpair.inj₁ H) = b₂ :=
  (dpair.inj H).2

end sigma

structure foo :=
mk :: (A : Type) (B : A → Type) (a : A) (b : B a)

set_option pp.implicit true

namespace foo
  open lift sigma sigma.ops
  universe variables l₁ l₂
  variables {A₁ : Type.{l₁}} {B₁ : A₁ → Type.{l₂}} {a₁ : A₁} {b₁ : B₁ a₁}
  variables {A₂ : Type.{l₁}} {B₂ : A₂ → Type.{l₂}} {a₂ : A₂} {b₂ : B₂ a₂}

  definition foo.inj (H : mk A₁ B₁ a₁ b₁ = mk A₂ B₂ a₂ b₂) :
    Σ (e₁ : A₁ = A₂) (e₂ : eq.rec B₁ e₁ = B₂) (e₃ : eq.rec a₁ e₁ = a₂), eq.rec (eq.rec (eq.rec b₁ e₁) e₂) e₃ = b₂ :=
  down (foo.no_confusion H (λ e₁ e₂ e₃ e₄, ⟨e₁, e₂, e₃, e₄⟩))

  definition foo.inj₁ (H : mk A₁ B₁ a₁ b₁ = mk A₂ B₂ a₂ b₂) : A₁ = A₂ :=
  (foo.inj H).1

  definition foo.inj₂ (H : mk A₁ B₁ a₁ b₁ = mk A₂ B₂ a₂ b₂) : eq.rec B₁ (foo.inj₁ H) = B₂ :=
  (foo.inj H).2.1

  definition foo.inj₃ (H : mk A₁ B₁ a₁ b₁ = mk A₂ B₂ a₂ b₂) : eq.rec a₁ (foo.inj₁ H) = a₂ :=
  (foo.inj H).2.2.1

  definition foo.inj₄ (H : mk A₁ B₁ a₁ b₁ = mk A₂ B₂ a₂ b₂) : eq.rec (eq.rec (eq.rec b₁ (foo.inj₁ H)) (foo.inj₂ H)) (foo.inj₃ H) = b₂ :=
  (foo.inj H).2.2.2

  definition foo.inj_inv (e₁ : A₁ = A₂) (e₂ : eq.rec B₁ e₁ = B₂) (e₃ : eq.rec a₁ e₁ = a₂) (e₄ : eq.rec (eq.rec (eq.rec b₁ e₁) e₂) e₃ = b₂) :
     mk A₁ B₁ a₁ b₁ = mk A₂ B₂ a₂ b₂ :=
  eq.rec_on e₄ (eq.rec_on e₃ (eq.rec_on e₂ (eq.rec_on e₁ rfl)))

end foo
