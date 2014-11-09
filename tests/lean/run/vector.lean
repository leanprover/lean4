import logic data.nat.basic
open nat

inductive vector (A : Type) : nat → Type :=
vnil  : vector A zero,
vcons : Π {n : nat}, A → vector A n → vector A (succ n)

namespace vector
  print definition no_confusion

  theorem vcons.inj₁ {A : Type} {n : nat} (a₁ a₂ : A) (v₁ v₂ : vector A n) : vcons a₁ v₁ = vcons a₂ v₂ → a₁ = a₂ :=
  begin
     intro h, apply (no_confusion h), intros, assumption
  end

  theorem vcons.inj₂ {A : Type} {n : nat} (a₁ a₂ : A) (v₁ v₂ : vector A n) : vcons a₁ v₁ = vcons a₂ v₂ → v₁ = v₂ :=
  begin
     intro h, apply heq.to_eq, apply (no_confusion h), intros, eassumption,
  end
end vector
