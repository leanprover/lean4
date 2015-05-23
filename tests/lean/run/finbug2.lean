/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Finite ordinals.
-/
open nat

inductive fin : nat → Type :=
| fz : Π n, fin (succ n)
| fs : Π {n}, fin n → fin (succ n)

namespace fin
  definition to_nat : Π {n}, fin n → nat
  | @to_nat (succ n) (fz n) := zero
  | @to_nat (succ n) (fs f) := succ (@to_nat n f)

  definition lift : Π {n : nat}, fin n → Π (m : nat), fin (add m n)
  | @lift (succ n) (fz n)     m := fz (add m n)
  | @lift (succ n) (@fs n f)  m := fs (@lift n f m)

  theorem to_nat_lift : ∀ {n : nat} (f : fin n) (m : nat), to_nat f = to_nat (lift f m)
  | to_nat_lift (fz n) m    := rfl
  | to_nat_lift (@fs n f) m := calc
      to_nat (fs f) = (to_nat f) + 1           : rfl
               ...  = (to_nat (lift f m)) + 1  : to_nat_lift f
               ...  = to_nat (lift (fs f) m)   : rfl
end fin
