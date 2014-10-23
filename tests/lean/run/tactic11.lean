import logic
open tactic

theorem tst (a b : Prop) (H : a ↔ b) : b ↔ a
:= have H1 [visible] : a → b, -- We need to mark H1 as fact, otherwise it is not visible by tactics
   from iff.elim_left H,
   by rapply iff.intro;
      apply (assume Ha, H1 Ha);
      apply (assume Hb, iff.elim_right H Hb)

theorem tst2 (a b : Prop) (H : a ↔ b) : b ↔ a
:= have H1 [visible] : a → b,
   from iff.elim_left H,
   begin
     rapply iff.intro,
     apply (assume Ha, H1 Ha),
     apply (assume Hb, iff.elim_right H Hb)
   end
