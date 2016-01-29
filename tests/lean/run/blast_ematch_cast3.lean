import data.nat
open nat

constant C : nat → Type₁
constant f : ∀ n, C n → C n
constant g : ∀ n, C n → C n → C n

lemma gffax [forward] (n : nat) (a b : C n) : (: g n a b :) = a :=
sorry

set_option blast.strategy "ematch"
set_option trace.blast.ematch true

example (n m : nat) (a c : C n) (b : C m) (e : m = n) : a == b → g n a a == b :=
by blast
