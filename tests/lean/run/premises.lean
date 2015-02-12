variable a : Prop
variables b c : Prop
premise  Ha : a
premises (Hb : b) (Hc : c)

theorem tst : a ∧ b ∧ c :=
and.intro Ha (and.intro Hb Hc)

check tst
