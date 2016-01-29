import data.nat
open nat

constant C : nat → Type₁
constant f : ∀ n, C n → C n
constant g : ∀ n, C n → C n → C n

lemma gffax [forward] (n : nat) (a b : C n) : (: g n (f n a) (f n b) :) = a :=
sorry

set_option blast.strategy "ematch"

example (n m : nat) (a c : C n) (b : C m) : n = m → a == f m b → g n a (f n c) == b :=
by blast
