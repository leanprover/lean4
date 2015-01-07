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
  definition to_nat : Π {n}, fin n → nat,
  @to_nat ⌞n+1⌟ (fz n) := zero,
  @to_nat ⌞n+1⌟ (fs f) := succ (to_nat f)

  theorem to_nat_fz (n : nat) : to_nat (fz n) = zero :=
  rfl

  theorem to_nat_fs {n : nat} (f : fin n) : to_nat (fs f) = succ (to_nat f) :=
  rfl

  theorem to_nat_lt : Π {n} (f : fin n), to_nat f < n,
  to_nat_lt (fz n) :=  calc
    to_nat (fz n) = 0    : rfl
             ...  < n+1  : succ_pos n,
  to_nat_lt (@fs n f) := calc
     to_nat (fs f) = (to_nat f)+1 : rfl
              ...  < n+1          : succ_lt_succ (to_nat_lt f)

  definition lift : Π {n : nat}, fin n → Π (m : nat), fin (m + n),
  @lift ⌞n+1⌟ (fz n)     m := fz (m + n),
  @lift ⌞n+1⌟ (@fs n f)  m := fs (lift f m)

  theorem lift_fz (n m : nat) : lift (fz n) m = fz (m + n) :=
  rfl

  theorem lift_fs {n : nat} (f : fin n) (m : nat) : lift (fs f) m = fs (lift f m) :=
  rfl

  theorem to_nat_lift : ∀ {n : nat} (f : fin n) (m : nat), to_nat f = to_nat (lift f m),
  to_nat_lift (fz n) m    := rfl,
  to_nat_lift (@fs n f) m := calc
      to_nat (fs f) = (to_nat f) + 1           : rfl
               ...  = (to_nat (lift f m)) + 1  : to_nat_lift f
               ...  = to_nat (lift (fs f) m)   : rfl

  definition of_nat : Π (p : nat) (n : nat), p < n → fin n,
  of_nat 0     0     h := absurd h (not_lt_zero zero),
  of_nat 0     (n+1) h := fz n,
  of_nat (p+1) 0     h := absurd h (not_lt_zero (succ p)),
  of_nat (p+1) (n+1) h := fs (of_nat p n (lt.of_succ_lt_succ h))

  theorem of_nat_zero_succ (n : nat) (h : 0 < n+1) : of_nat 0 (n+1) h = fz n :=
  rfl

  theorem of_nat_succ_succ (p n : nat) (h : p+1 < n+1) :
               of_nat (p+1) (n+1) h = fs (of_nat p n (lt.of_succ_lt_succ h)) :=
  rfl

  theorem to_nat_of_nat : ∀ (p : nat) (n : nat) (h : p < n), to_nat (of_nat p n h) = p,
  to_nat_of_nat 0     0     h := absurd h (not_lt_zero 0),
  to_nat_of_nat 0     (n+1) h := rfl,
  to_nat_of_nat (p+1) 0     h := absurd h (not_lt_zero (p+1)),
  to_nat_of_nat (p+1) (n+1) h := calc
    to_nat (of_nat (p+1) (n+1) h)
             = succ (to_nat (of_nat p n _)) : rfl
         ... = succ p                       : to_nat_of_nat p n _

  theorem of_nat_to_nat : ∀ {n : nat} (f : fin n) (h : to_nat f < n), of_nat (to_nat f) n h = f,
  of_nat_to_nat (fz n) h    := rfl,
  of_nat_to_nat (@fs n f) h := calc
    of_nat (to_nat (fs f)) (succ n) h = fs (of_nat (to_nat f) n _) : rfl
                                 ...  = fs f                       : of_nat_to_nat f _

end fin
