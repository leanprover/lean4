import data.nat
open nat

inductive functor (A B : Type) :=
mk : (A → B) → functor A B

definition functor.to_fun [coercion] {A B : Type} (f : functor A B) : A → B :=
functor.rec (λ f, f) f

inductive struct :=
mk : Π (A : Type), (A → A → Prop) → struct

definition struct.to_sort [coercion] (s : struct) : Type :=
struct.rec (λA r, A) s

definition g (f : nat → nat) (a : nat) := f a

constant f : functor nat nat

check g (functor.to_fun f) 0

check g f 0

definition id (A : Type) (a : A) := a

constant S : struct
constant a : S

check id (struct.to_sort S) a
check id S a
