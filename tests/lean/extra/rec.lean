import data.vector
open nat vector

check lt.base
set_option pp.implicit true

definition add : nat → nat → nat,
add zero b     := b,
add (succ a) b := succ (add a b)

definition map {A B C : Type} (f : A → B → C) : Π {n}, vector A n → vector B n → vector C n,
map nil nil             := nil,
map (a :: va) (b :: vb) := f a b :: map va vb

definition fib : nat → nat,
fib 0     := 1,
fib 1     := 1,
fib (a+2) := (fib a ↓ lt.step (lt.base a)) + (fib (a+1) ↓ lt.base (a+1))
[wf] lt.wf

definition half : nat → nat,
half 0     := 0,
half 1     := 0,
half (x+2) := half x + 1

variables {A B : Type}
inductive image_of (f : A → B) : B → Type :=
mk : Π a, image_of f (f a)

definition inv {f : A → B} : Π b, image_of f b → A,
inv ⌞f a⌟ (image_of.mk f a) := a
