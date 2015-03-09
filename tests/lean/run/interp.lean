import algebra.function
open bool nat
open function

inductive univ :=
| ubool  : univ
| unat   : univ
| uarrow : univ → univ → univ

open univ

definition interp : univ → Type₁
| ubool          := bool
| unat           := nat
| (uarrow fr to) := interp fr → interp to

definition foo : Π (u : univ) (el : interp u), interp u
| ubool          tt := ff
| ubool          ff := tt
| unat           n  := succ n
| (uarrow fr to) f  := λ x : interp fr, f (foo fr x)

definition is_even : nat → bool
| zero     := tt
| (succ n) := bnot (is_even n)

example : foo unat 10  = 11 := rfl
example : foo ubool tt = ff := rfl
example : foo (uarrow unat ubool) (λ x : nat, is_even x) 3 = tt := rfl
example : foo (uarrow unat ubool) (λ x : nat, is_even x) 4 = ff := rfl
