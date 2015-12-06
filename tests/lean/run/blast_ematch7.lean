import algebra.ring data.int
open algebra

variables {A : Type} [s : ring A] (a b : A)
include s

set_option blast.strategy "ematch"

attribute zero_mul [forward]

example : a = 0 → a * b = 0 :=
by blast

open int

definition ex1 (a b : int) : a = 0 → a * b = 0 :=
by blast

print ex1
