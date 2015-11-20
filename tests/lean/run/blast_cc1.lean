import data.list

constant f {A : Type} : A → A → A
constant g : nat → nat
set_option blast.subst false

example (a b c : nat) : a = b → g a == g b :=
by blast

example (a b c : nat) : a = b → c = b → f (f a b) (g c) = f (f c a) (g b) :=
by blast

example (a b c d e x y : nat) : a = b → a = x → b = y → c = d → c = e → c = b → a = e :=
by blast

open perm

example (a b c d : list nat) : a ~ b → c ~ b → d ~ c → a ~ d :=
by blast

example (a b c d : list nat) : a ~ b → c ~ b → d = c → a ~ d :=
by blast
