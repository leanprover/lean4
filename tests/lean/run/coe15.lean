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

check
  λ f,
    (g f 0) = 0 ∧ (functor.to_fun f) 0 = 0
