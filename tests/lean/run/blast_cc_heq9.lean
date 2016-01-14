example (f g : Π {A : Type₁}, A → A → A) (h : nat → nat) (a b : nat) :
        h = f a → h b = f a b :=
by blast


example (f g : Π {A : Type₁} (a b : A), A) (h : nat → nat) (a b : nat) :
        h = f a → h b = f a b :=
by blast
