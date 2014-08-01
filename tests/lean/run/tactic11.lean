import standard
using tactic

theorem tst (a b : Prop) (H : a ↔ b) : b ↔ a
:= have H1 [fact] : a → b, -- We need to mark H1 as fact, otherwise it is not visible by tactics
   from iff_elim_left H,
   by apply iff_intro;
      apply (assume Hb, iff_elim_right H Hb);
      apply (assume Ha, H1 Ha)
