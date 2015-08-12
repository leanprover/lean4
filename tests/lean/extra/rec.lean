import data.examples.vector
open nat vector

definition fib : nat → nat,
fib 0     := 1,
fib 1     := 1,
fib (a+2) := (fib a ↓ lt.step (lt.base a)) + (fib (a+1) ↓ lt.base (a+1))
[wf] lt.wf

definition gcd : nat → nat → nat,
gcd 0 x               := x,
gcd x 0               := x,
gcd (succ x) (succ y) := if y ≤ x
                         then gcd (x - y) (succ y) ↓ !sigma.lex.left (lt_succ_of_le (sub_le x y))
                         else gcd (succ x) (y - x) ↓ !sigma.lex.right (lt_succ_of_le (sub_le y x))
[wf] sigma.lex.wf lt.wf (λ x, lt.wf)

definition add : nat → nat → nat,
add zero b     := b,
add (succ a) b := succ (add a b)

definition map {A B C : Type} (f : A → B → C) : Π {n}, vector A n → vector B n → vector C n,
map nil nil             := nil,
map (a :: va) (b :: vb) := f a b :: map va vb

definition half : nat → nat,
half 0     := 0,
half 1     := 0,
half (x+2) := half x + 1

variables {A B : Type}
inductive image_of (f : A → B) : B → Type :=
mk : Π a, image_of f (f a)

definition inv {f : A → B} : Π b, image_of f b → A,
inv ⌞f a⌟ (image_of.mk f a) := a

namespace tst

definition fib : nat → nat,
fib 0     := 1,
fib 1     := 1,
fib (a+2) := fib a + fib (a+1)

end tst

definition simple : nat → nat → nat,
simple x y := x + y

definition simple2 : nat → nat → nat,
simple2 (x+1) y := x + y,
simple2 ⌞y+1⌟ y := y



check @vector.brec_on
check @vector.cases_on
