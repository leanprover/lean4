constant subt : nat → nat → Prop

lemma subt_trans [forward] {a b c : nat} : subt a b → subt b c → subt a c :=
sorry

set_option blast.strategy "ematch"

example (a b c d : nat) : subt a b → subt b c → subt c d → subt a d :=
by blast
