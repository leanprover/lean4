import logic data.nat.basic data.prod data.unit
open nat prod

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

  section
    universe variables l₁ l₂
    variable {A : Type.{l₁}}
    variable C : Π (n : nat), vector A n → Type.{l₂}
    definition below {n : nat} (v : vector A n) :=
    rec_on v unit.{max 1 l₂} (λ (n₁ : nat) (a₁ : A) (v₁ : vector A n₁) (r₁ : Type.{max 1 l₂}), C n₁ v₁ × r₁)
  end

  section
    universe variables l₁ l₂
    variable {A : Type.{l₁}}
    variable {C : Π (n : nat), vector A n → Type.{l₂}}
    definition brec_on {n : nat} (v : vector A n) (H : Π (n : nat) (v : vector A n), below C v → C n v) : C n v :=
    have general : C n v × below C v, from
      rec_on v
       (pair (H zero (vnil A) unit.star) unit.star)
       (λ (n₁ : nat) (a₁ : A) (v₁ : vector A n₁) (r₁ : C n₁ v₁ × below C v₁),
          have b : below C (vcons a₁ v₁), from
            r₁,
          have c : C (succ n₁) (vcons a₁ v₁), from
            H (succ n₁) (vcons a₁ v₁) b,
          pair c b),
    pr₁ general
  end

  check brec_on

end vector
