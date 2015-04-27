import logic

theorem tst (a b : Prop) (H : a ↔ b) : b ↔ a
:= by apply iff.intro;
      intro Hb;
        apply (iff.elim_right H Hb);
      intro Ha;
        apply (iff.elim_left H Ha)

check tst
