universe l
constants (A : Type.{l}) (P : A → Prop) (h : Π (a : A), P a → A) (f g : A → A)
constants (p : ∀ a, P a)

axiom h_simp {a : A} : h (f a) (p (f a)) = a
attribute h_simp [simp]

example {a b : A} : g b = f a → h (g b) (p (g b)) = a :=
by inst_simp
