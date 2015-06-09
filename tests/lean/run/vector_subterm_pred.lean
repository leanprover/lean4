import logic data.nat.basic data.sigma
open nat eq.ops sigma

inductive vector (A : Type) : nat → Type :=
| nil  : vector A zero
| cons : A → (Π{n}, vector A n → vector A (succ n))

namespace vector

definition vec (A : Type) : Type := Σ n : nat, vector A n

definition to_vec {A : Type} {n : nat} (v : vector A n) : vec A := ⟨n, v⟩

inductive direct_subterm (A : Type) : vec A → vec A → Prop :=
cons : Π (n : nat) (a : A) (v : vector A n), direct_subterm A (to_vec v) (to_vec (cons a v))

definition direct_subterm.wf (A : Type) : well_founded (direct_subterm A) :=
well_founded.intro (λ (bv : vec A),
  sigma.rec_on bv (λ (n : nat) (v : vector A n),
      vector.rec_on v
        (show acc (direct_subterm A) (to_vec (nil A)), from
          acc.intro (to_vec (nil A)) (λ (v₂ : vec A) (H : direct_subterm A v₂ (to_vec (nil A))),
            have gen : ∀ (bv : vec A) (H : direct_subterm A v₂ bv) (Heq : bv = (to_vec (nil A))), acc (direct_subterm A) v₂, from
              λ bv H, direct_subterm.induction_on H (λ n₁ a₁ v₁ e,
                have e₁ : succ n₁ = zero, from sigma.no_confusion e (λ e₁ e₂, e₁),
                nat.no_confusion e₁),
            gen (to_vec (nil A)) H rfl))
        (λ (a₁ : A) (n₁ : nat) (v₁ : vector A n₁) (ih : acc (direct_subterm A) (to_vec v₁)),
          acc.intro (to_vec (cons a₁ v₁)) (λ (w₁ : vec A) (lt₁ : direct_subterm A w₁ (to_vec (cons a₁ v₁))),
            have gen : ∀ (bv : vec A) (H : direct_subterm A w₁ bv) (Heq : bv = (to_vec (cons a₁ v₁))), acc (direct_subterm A) w₁, from
              λ bv H, direct_subterm.induction_on H (λ n₂ a₂ v₂ e,
                sigma.no_confusion e (λ (e₁ : succ n₂ = succ n₁) (e₂ : @cons A a₂ n₂ v₂ == @cons A a₁ n₁ v₁),
                nat.no_confusion e₁ (λ (e₃ : n₂ = n₁),
                have gen₂ : ∀ (m : nat) (Heq₁ : n₂ = m) (v : vector A m) (ih : acc (direct_subterm A) (to_vec v))
                              (Heq₂ : @cons A a₂ n₂ v₂ == @cons A a₁ m v), acc (direct_subterm A) (to_vec v₂), from
                  λ m Heq₁, eq.rec_on Heq₁ (λ (v : vector A n₂) (ih : acc (direct_subterm A) (to_vec v)) (Heq₂ : @cons A a₂ n₂ v₂ == @cons A a₁ n₂ v),
                    vector.no_confusion (heq.to_eq Heq₂) (λ (e₄ : a₂ = a₁) (e₅ : n₂ = n₂) (e₆ : v₂ == v),
                      eq.rec_on (heq.to_eq (heq.symm e₆)) ih)),
                gen₂ n₁ e₃ v₁ ih e₂))),
            gen (to_vec (cons a₁ v₁)) lt₁ rfl))))

definition direct_subterm.wf₂ (A : Type) : well_founded (direct_subterm A) :=
begin
  constructor, intro V, cases V with n v, induction v,
  repeat (constructor; intro y hlt; cases hlt; repeat assumption)
end

definition subterm (A : Type) := tc (direct_subterm A)

definition subterm.wf (A : Type) : well_founded (subterm A) :=
tc.wf (direct_subterm.wf A)
end vector
