import logic

theorem tst (a b : Prop) (H : a ↔ b) : b ↔ a
:= by rapply iff.intro;
      intro Ha;
        apply (iff.elim_left H Ha);
      intro Hb;
        apply (iff.elim_right H Hb)

check tst
