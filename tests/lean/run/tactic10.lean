import logic
open tactic

theorem tst (a b : Prop) (H : a ↔ b) : b ↔ a
:= by rapply iff.intro;
      apply (assume Ha, iff.elim_left H Ha);
      apply (assume Hb, iff.elim_right H Hb)

check tst
