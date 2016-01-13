constant q (a : Prop) (h : decidable a) : Prop
constant r : nat → Prop
constant rdec : ∀ a, decidable (r a)
constant s : nat → nat

axiom qax : ∀ a h, (: q (r (s a)) h :)
attribute qax [forward]

set_option blast.strategy "ematch"

definition ex1 (a : nat) (b : nat) : b = s a → q (r b) (rdec b) :=
by blast

print ex1
