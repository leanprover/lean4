open tactic

example (f g : Π {α : Type}, α → α → α) (h : nat → nat) (a b : nat) :
        h = f a → h b = f a b :=
by cc

example (f g : Π {α : Type} (a b : α), {x : α // x ≠ b}) (h : Π (b : nat), {x : nat // x ≠ b}) (a b₁ b₂ : nat) :
        h = f a → b₁ = b₂ → h b₁ == f a b₂ :=
by cc

example (f : nat → nat → nat) (a b c d : nat) :
        c = d → f a = f b → f a c = f b d :=
by cc

example (f : nat → nat → nat) (a b c d : nat) :
        c == d → f a == f b → f a c == f b d :=
by cc
