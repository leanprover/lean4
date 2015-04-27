import logic

theorem tst (a b : Prop) (H : a ↔ b) : b ↔ a
:= have H1 [visible] : a → b, -- We need to mark H1 as fact, otherwise it is not visible by tactics
   from iff.elim_left H,
   by apply iff.intro;
      intro Hb;
        apply (iff.elim_right H Hb);
      intro Ha;
        apply (H1 Ha)

theorem tst2 (a b : Prop) (H : a ↔ b) : b ↔ a
:= have H1 [visible] : a → b,
   from iff.elim_left H,
   begin
     apply iff.intro,
     intro Hb;
       apply (iff.elim_right H Hb),
     intro Ha;
       apply (H1 Ha)
   end
