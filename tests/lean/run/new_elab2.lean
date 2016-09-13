set_option new_elaborator true

theorem ex {a : Prop} (H : ¬a) : a ↔ false :=
iff.intro H (false.rec a)
