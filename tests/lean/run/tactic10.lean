import standard
using tactic

theorem tst (a b : Bool) (H : a ↔ b) : b ↔ a
:= by apply iff_intro;
      ⟦ assume Hb, iff_mp_right H Hb ⟧;
      ⟦ assume Ha, iff_mp_left H Ha ⟧

check tst
