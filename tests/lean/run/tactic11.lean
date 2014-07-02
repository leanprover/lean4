import logic

exit -- TODO
theorem tst (a b : Bool) (H : a ↔ b) : b ↔ a
:= have H1 [fact] : a → b, from iff_elim_left H,
   by (apply iff_intro,
       assume Hb, iff_mp_right H Hb,
       assume Ha, H1 Ha)
