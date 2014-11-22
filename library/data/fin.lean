import data.nat logic.cast
open nat

inductive fin : nat → Type :=
fz : Π n, fin (succ n),
fs : Π {n}, fin n → fin (succ n)

namespace fin

  definition z_cases_on (C : fin zero → Type) (p : fin zero) : C p :=
  have aux : Π (C : Type) (n : nat) (p : fin n), n = zero → C, from
    λ C n p, fin.rec_on p
      (λ n h, nat.no_confusion h)
      (λ n f ih h, nat.no_confusion h),
  aux (C p) zero p rfl

  definition nz_cases_on {C  : Π n, fin (succ n) → Type}
                         (H₁ : Π n, C n (fz n))
                         (H₂ : Π n (f : fin n), C n (fs f))
                         {n  : nat}
                         (f  : fin (succ n)) : C n f :=
  have aux : Π (n₁ : nat) (f₁ : fin n₁) (heq₁ : n₁ = succ n) (f : fin (succ n)) (heq₂ : f₁ == f), C n f, from
    λ n₁ f₁, fin.rec_on f₁
      (λ (n₁ : nat) (heq₁ : succ n₁ = succ n),
         have heq₁' : n₁ = n, from nat.no_confusion heq₁ (λ e, e),
         eq.rec_on heq₁' (λ (f : fin (succ n₁)) (heq₂ : fz n₁ == f),
           have heq₂' : fz n₁ = f, from heq.to_eq heq₂,
           have Cfz   : C n₁ (fz n₁), from H₁ n₁,
           eq.rec_on heq₂' Cfz))
      (λ (n₁ : nat) (f₁ : fin n₁) (ih : _) (heq₁ : succ n₁ = succ n),
         have heq₁' : n₁ = n, from nat.no_confusion heq₁ (λ e, e),
         eq.rec_on heq₁' (λ (f : fin (succ n₁)) (heq₂ : @fs n₁ f₁ == f),
           have heq₂' : @fs n₁ f₁ = f, from heq.to_eq heq₂,
           have Cfs   : C n₁ (@fs n₁ f₁), from H₂ n₁ f₁,
           eq.rec_on heq₂' Cfs)),
  aux (succ n) f rfl f !heq.refl

  definition to_nat {n : nat} (f : fin n) : nat :=
  fin.rec_on f
    (λ n, zero)
    (λ n f r, succ r)

  theorem to_nat.lt {n : nat} (f : fin n) : to_nat f < n :=
  fin.rec_on f
    (λ n, calc
      to_nat (fz n) = 0          : rfl
               ...  < succ n     : succ_pos n)
    (λ n f ih, calc
      to_nat (fs f) = succ (to_nat f) : rfl
               ...  < succ n          : succ_lt ih)

  definition lift {n : nat} (f : fin n) : Π m, fin (m + n) :=
  fin.rec_on f
    (λ n m, fz (m + n))
    (λ n f ih m, fs (ih m))

  theorem to_nat.lift {n : nat} (f : fin n) : ∀m, to_nat f = to_nat (lift f m) :=
  fin.rec_on f
    (λ n m, rfl)
    (λ n f ih m, calc
      to_nat (fs f) = succ (to_nat f)          : rfl
               ...  = succ (to_nat (lift f m)) : ih
               ...  = to_nat (lift (fs f) m)   : rfl)

  private definition of_nat_core (p : nat) : fin (succ p) :=
  nat.rec_on p
    (fz zero)
    (λ a r, fs r)

  private theorem to_nat.of_nat_core (p : nat) : to_nat (of_nat_core p) = p :=
  nat.induction_on p
    rfl
    (λ p₁ ih, calc
       to_nat (of_nat_core (succ p₁)) = succ (to_nat (of_nat_core p₁)) : rfl
                                ...   = succ p₁                        : ih)

  private lemma of_nat_eq {p n : nat} (H : p < n) : n - succ p + succ p = n :=
  add_sub_ge_left (lt_imp_le_succ H)

  definition of_nat (p : nat) (n : nat) : p < n → fin n :=
  λ H : p < n,
    eq.rec_on (of_nat_eq H) (lift (of_nat_core p) (n - succ p))

  theorem of_nat_def (p : nat) (n : nat) (H : p < n) : of_nat p n H = eq.rec_on (of_nat_eq H) (lift (of_nat_core p) (n - succ p)) :=
  rfl

  theorem of_nat_heq (p : nat) (n : nat) (H : p < n) : of_nat p n H == lift (of_nat_core p) (n - succ p) :=
  heq.symm (eq_rec_to_heq (eq.symm (of_nat_def p n H)))

  theorem to_nat.of_nat (p : nat) (n : nat) (H : p < n) : to_nat (of_nat p n H) = p :=
  have aux₁ : to_nat (of_nat p n H)  == to_nat (lift (of_nat_core p) (n - succ p)), from
    hcongr_arg2 @to_nat (eq.symm (of_nat_eq H)) (of_nat_heq p n H),
  have aux₂ : to_nat (lift (of_nat_core p) (n - succ p)) = p, from calc
    to_nat (lift (of_nat_core p) (n - succ p)) = to_nat (of_nat_core p) : to_nat.lift
                                         ...   = p                      : to_nat.of_nat_core,
  heq.to_eq (heq.trans aux₁ (heq.from_eq aux₂))

end fin
