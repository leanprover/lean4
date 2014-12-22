/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.fin
Author: Leonardo de Moura

Finite ordinals.
-/

import data.nat logic.cast
open nat

inductive fin : nat → Type :=
fz : Π n, fin (succ n),
fs : Π {n}, fin n → fin (succ n)

namespace fin

  definition z_cases_on (C : fin zero → Type) (p : fin zero) : C p :=
  by cases p

  definition nz_cases_on {C  : Π n, fin (succ n) → Type}
                         (H₁ : Π n, C n (fz n))
                         (H₂ : Π n (f : fin n), C n (fs f))
                         {n  : nat}
                         (f  : fin (succ n)) : C n f :=
  begin
    cases f with (n', n', f'),
    apply (H₁ n'),
    apply (H₂ n' f')
  end

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
  add_sub_ge_left (succ_le_of_lt H)

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
  heq.to_eq (heq.trans aux₁ (heq.of_eq aux₂))

end fin
