import standard
using tactic

theorem tst (a b : Bool) (H : a ↔ b) : b ↔ a
:= have H1 [fact] : a → b, -- We need to mark H1 as fact, otherwise it is not visible by tactics
   from iff_elim_left H,
   by ⟦ iff_intro ⟧;
      ⟦ assume Hb, iff_mp_right H Hb ⟧;
      ⟦ assume Ha, H1 Ha ⟧
