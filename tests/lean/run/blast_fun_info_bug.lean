definition set (A : Type) := A → Prop

example {A : Type} (s : set A) (a b : A) : a = b → s a → s b :=
by blast
