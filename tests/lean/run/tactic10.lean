import logic
open tactic

theorem tst (a b : Prop) (H : a ↔ b) : b ↔ a
:= by apply iff.intro;
      apply (assume Hb, iff.elim_right H Hb);
      apply (assume Ha, iff.elim_left H Ha)

check tst
