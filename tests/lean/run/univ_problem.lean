import logic data.nat.basic data.prod
open nat prod

inductive vector (A : Type) : nat → Type :=
| vnil {} : vector A zero
| vcons   : Π {n : nat}, A → vector A n → vector A (succ n)

namespace vector
  print definition vector.no_confusion
  infixr `::` := vcons

  namespace play
  section
    universe variables l₁ l₂
    variable {A : Type.{l₁}}
    variable {C : Π (n : nat), vector A n → Type.{l₂+1}}
    definition brec_on {n : nat} (v : vector A n) (H : Π (n : nat) (v : vector A n), @vector.below A C n v → C n v) : C n v :=
    have general : C n v × @vector.below A C n v, from
      vector.rec_on v
       (pair (H zero vnil poly_unit.star) poly_unit.star)
       (λ (n₁ : nat) (a₁ : A) (v₁ : vector A n₁) (r₁ : C n₁ v₁ × @vector.below A C n₁ v₁),
          have b : @vector.below A C _ (vcons a₁ v₁), from
            r₁,
          have c : C (succ n₁) (vcons a₁ v₁), from
            H (succ n₁) (vcons a₁ v₁) b,
          pair c b),
    pr₁ general
  end
  end play

end vector
