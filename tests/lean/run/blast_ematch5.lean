constant subt : nat → nat → Prop

lemma subt_trans [forward] {a b c : nat} : subt a b → subt b c → subt a c :=
sorry

set_option blast.init_depth 20
set_option blast.inc_depth  100
set_option blast.ematch   true
set_option blast.simp     false
-- TODO(Leo): check if unit propagation is still buggy
-- If I remove the following option, blast fails
set_option blast.backward true -- false

example (a b c d : nat) : subt a b → subt b c → subt c d → subt a d :=
by blast
