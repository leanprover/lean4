import logic data.nat.basic
open nat

inductive vector (A : Type) : nat → Type :=
| vnil  : vector A zero
| vcons : Π {n : nat}, A → vector A n → vector A (succ n)

namespace vector
  theorem vcons.inj₁ {A : Type} {n : nat} (a₁ a₂ : A) (v₁ v₂ : vector A n) : vcons a₁ v₁ = vcons a₂ v₂ → a₁ = a₂ :=
  assume h, vector.no_confusion h (λ n h t, h)

end vector
