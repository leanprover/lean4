import logic
open tactic

theorem tst (a b : Prop) (H : a ↔ b) : b ↔ a
:= have H1 [fact] : a → b, -- We need to mark H1 as fact, otherwise it is not visible by tactics
   from iff.elim_left H,
   by apply iff.intro;
      apply (assume Hb, iff.elim_right H Hb);
      apply (assume Ha, H1 Ha)
