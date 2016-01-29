import data.nat
open nat

constant C : nat → Type₁
constant f : ∀ n, C n → C n

lemma fax [forward] (n : nat) (a : C (2*n)) : (: f (2*n) a :) = a :=
sorry

set_option blast.strategy "ematch"

example (n m : nat) (a : C n) : n = 2*m → f n a = a :=
by blast
