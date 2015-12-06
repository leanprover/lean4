set_option blast.ematch true
variable {A : Type}
definition R : A → A → Prop := sorry
definition R_trans [forward] {a b c : A} : R a b → R b c → R a c := sorry

example (a b c : A) : R a b → R b c → R a c :=
by blast

example {A : Type} (a b c : A) : R a b → R b c → R a c :=
by blast

example {A : Type.{1}} (a b c : A) : R a b → R b c → R a c :=
by blast

universe u
example {A : Type.{u}} (a b c : A) : R a b → R b c → R a c :=
by blast
