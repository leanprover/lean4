import data.nat
open nat

lemma aux : ∃ x : nat, x > 10 :=
exists.intro 15 dec_trivial

vm_eval nat.find aux
