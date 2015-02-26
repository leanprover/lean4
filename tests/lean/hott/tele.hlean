-- check @eq.rec
-- universe variable l_1
-- variables {A A' : Type.{l_1}} {e_1 : A = A'} {a : A}
-- check @eq.rec.{l_1 l_1+1} Type.{l_1} A (fun (A' : Type.{l_1}) (e_1 : A = A'), A') a A' e_1
open nat

inductive vec (A : Type) : nat → Type :=
| nil {} : vec A zero
| cons   : Π {n}, A → vec A n → vec A (succ n)

structure S (A : Type) (a : A) (n : nat) (v : vec A n) :=
mk :: (fa : A)

set_option pp.implicit true

#telescope_eq Π (A : Type) (a : A) (b : A) (c : nat) (d : vec A c) (e : S A a c d), nat
