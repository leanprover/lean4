import logic
using tactic

theorem tst (a b : Prop) (H : a ↔ b) : b ↔ a
:= by apply iff_intro;
      apply (assume Hb, iff_elim_right H Hb);
      apply (assume Ha, iff_elim_left H Ha)

check tst
