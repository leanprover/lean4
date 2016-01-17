open subtype
set_option blast.strategy "cc"

example (f g : Π {A : Type₁}, A → A → A) (h : nat → nat) (a b : nat) :
        h = f a → h b = f a b :=
by blast

example (f g : Π {A : Type₁}, A → A → A) (h : nat → nat) (a b : nat) :
        h = f a → h b = f a b :=
by blast

example (f g : Π {A : Type₁} (a b : A), {x : A | x ≠ b}) (h : Π (b : nat), {x : nat | x ≠ b}) (a b₁ b₂ : nat) :
        h = f a → b₁ = b₂ → h b₁ == f a b₂ :=
by blast
