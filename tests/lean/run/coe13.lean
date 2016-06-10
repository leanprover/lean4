import data.nat
open nat

inductive Functor (A B : Type) :=
mk : (A → B) → Functor A B

definition Functor.to_fun [coercion] {A B : Type} (f : Functor A B) : A → B :=
Functor.rec (λ f, f) f

inductive struct :=
mk : Π (A : Type), (A → A → Prop) → struct

definition struct.to_sort [coercion] (s : struct) : Type :=
struct.rec (λA r, A) s

definition g (f : nat → nat) (a : nat) := f a

constant f : Functor nat nat

check g (Functor.to_fun f) 0

check g f 0


constant S : struct
constant a : S

check @id (struct.to_sort S) a
check @id S a
