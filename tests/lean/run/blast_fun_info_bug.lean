definition set (A : Type) := A → Prop
set_option blast.strategy "preprocess"

example {A : Type} (s : set A) (a b : A) : a = b → s a → s b :=
by blast

set_option blast.strategy "cc"

example {A : Type} (s : set A) (a b : A) : a = b → s a → s b :=
by blast
