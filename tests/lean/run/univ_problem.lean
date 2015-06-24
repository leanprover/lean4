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

  print "====================="
  definition append {A : Type} {n m : nat} (w : vector A m) (v : vector A n) : vector A (n + m) :=
  vector.brec_on w (λ (n : nat) (w : vector A n),
    vector.cases_on w
      (λ (B : vector.below vnil), v)
      (λ (n₁ : nat) (a₁ : A) (v₁ : vector A n₁) (B : vector.below (vcons a₁ v₁)),
         vcons a₁ (pr₁ B)))

  exit
  check vector.brec_on
  definition bw := @vector.below

  definition sum {n : nat} (v : vector nat n) : nat :=
  vector.brec_on v (λ (n : nat) (v : vector nat n),
    vector.cases_on v
      (λ (B : bw vnil), zero)
      (λ (n₁ : nat) (a : nat) (v₁ : vector nat n₁) (B : bw (vcons a v₁)),
         a + pr₁ B))

  example :  sum (10 :: 20 :: vnil) = 30 :=
  rfl

  definition addk {n : nat} (v : vector nat n) (k : nat) : vector nat n :=
  vector.brec_on v (λ (n : nat) (v : vector nat n),
    vector.cases_on v
      (λ (B : bw vnil), vnil)
      (λ (n₁ : nat) (a₁ : nat) (v₁ : vector nat n₁) (B : bw (vcons a₁ v₁)),
         vcons (a₁+k) (pr₁ B)))

  example : addk (1 :: 2 :: vnil) 3 = 4 :: 5 :: vnil :=
  rfl

  example : append (1 :: 2 :: vnil) (3 :: vnil) = 1 :: 2 :: 3 :: vnil :=
  rfl

  definition head {A : Type} {n : nat} (v : vector A (succ n)) : A :=
  nat.cases_on v
    (λ H : succ n = 0, nat.no_confusion H)
    (λn' h t (H : succ n = succ n'), h)
    rfl

  definition tail {A : Type} {n : nat} (v : vector A (succ n)) : vector A n :=
  @nat.cases_on A (λn' v, succ n = n' → vector A (pred n')) (succ n) v
    (λ H : succ n = 0, nat.no_confusion H)
    (λ (n' : nat) (h : A) (t : vector A n') (H : succ n = succ n'),
       t)
    rfl

  definition add {n : nat} (w v : vector nat n) : vector nat n :=
  @nat.brec_on nat (λ (n : nat) (v : vector nat n), vector nat n → vector nat n) n w
  (λ (n : nat) (w : vector nat n),
    vector.cases_on w
      (λ (B : bw vnil) (w : vector nat zero), vnil)
      (λ (n₁ : nat) (a₁ : nat) (v₁ : vector nat n₁) (B : bw (vcons a₁ v₁)) (v : vector nat (succ n₁)),
         vcons (a₁ + head v) (pr₁ B (tail v)))) v

  example : add (1 :: 2 :: vnil) (3 :: 5 :: vnil) = 4 :: 7 :: vnil :=
  rfl

end vector
