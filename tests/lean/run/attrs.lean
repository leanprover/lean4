structure A : Type :=
(a : nat)

structure B : Type :=
(a : nat)

structure C : Type :=
(a : nat)

constant f : A → B
constant g : B → C
constant h : C → C
constant a : A

attribute f g [coercion]
set_option pp.coercions true
set_option pp.beta true

check h a
