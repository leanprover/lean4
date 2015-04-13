import data.fintype data.list data.sum data.nat
open option list nat

structure countable [class] (A : Type) :=
(pickle : A → nat) (unpickle : nat → option A) (picklek : ∀ a, unpickle (pickle a) = some a)

open countable

definition countable_fintype [instance] {A : Type} [h₁ : fintype A] [h₂ : decidable_eq A] : countable A :=
countable.mk
  (λ a, find a (elements_of A))
  (λ n, nth (elements_of A) n)
  (λ a, find_nth (fintype.complete a))

definition countable_nat [instance] : countable nat :=
countable.mk (λ a, a) (λ n, some n) (λ a, rfl)

definition countable_option [instance] {A : Type} [h : countable A] : countable (option A) :=
countable.mk
  (λ o, match o with
        | some a := succ (pickle a)
        | none := 0
        end)
  (λ n, if n = 0 then some none else some (unpickle A (pred n)))
  (λ o,
    begin
    cases o with [a],
      begin esimp end,
      begin esimp, rewrite [if_neg !succ_ne_zero, pred_succ, countable.picklek] end
    end)

section sum
variables {A B : Type}
variables [h₁ : countable A] [h₂ : countable B]
include h₁ h₂

definition pickle_sum : sum A B → nat
| (sum.inl a) := 2 * pickle a
| (sum.inr b) := 2 * pickle b + 1

definition unpickle_sum (n : nat) : option (sum A B) :=
if n mod 2 = 0 then
   match unpickle A (n div 2) with
   | some a := some (sum.inl a)
   | none   := none
   end
else
   match unpickle B ((n - 1) div 2) with
   | some b := some (sum.inr b)
   | none   := none
   end

open decidable
theorem unpickle_pickle_sum : ∀ s : sum A B, unpickle_sum (pickle_sum s) = some s
| (sum.inl a) :=
  assert aux : 2 > 0, from dec_trivial,
  begin
    esimp [pickle_sum, unpickle_sum],
    rewrite [mul_mod_right, if_pos (eq.refl 0), mul_div_cancel_left _ aux, countable.picklek]
  end
| (sum.inr b) :=
  assert aux₁ : 2 > 0,       from dec_trivial,
  assert aux₂ : 1 mod 2 = 1, by rewrite [modulo_def],
  assert aux₃ : 1 ≠ 0,       from dec_trivial,
  begin
    esimp [pickle_sum, unpickle_sum],
    rewrite [add.comm, add_mul_mod_self_left aux₁, aux₂, if_neg aux₃, add_sub_cancel_left,
             mul_div_cancel_left _ aux₁, countable.picklek]
  end

definition countable_sum [instance] {A B : Type} [h₁ : countable A] [h₂ : countable B] : countable (sum A B) :=
countable.mk
  (λ s, pickle_sum s)
  (λ n, unpickle_sum n)
  (λ s, unpickle_pickle_sum s)

end sum
