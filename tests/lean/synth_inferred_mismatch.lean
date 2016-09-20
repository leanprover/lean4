
constant f   (c : Prop) [decidable c] : Prop
constant fax (c : Prop) [decidable c] : f c
attribute [elab_simple] fax

example (c : Prop) [decidable c] (h : c) : f c :=
(fax _ : @f c (is_true h))
