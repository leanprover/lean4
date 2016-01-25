constant p : nat → Prop
constant q : Π a, p a → Prop

set_option blast.strategy "unit"

example (a : nat) (h₁ : p a) (h₂ : ∀ h : p a, q a h) : q a h₁ :=
by blast

example (a : nat) (h₂ : ∀ h : p a, q a h) (h₁ : p a) : q a h₁ :=
by blast

example (a b : nat) (H : ∀ (p₁ : p a) (p₂ : p b), q b p₂ → q a p₁) (h₁ : p a) (h₂ : p b) : q b h₂ → q a h₁ :=
by blast

example (a b : nat) (h₂ : p b) (H : ∀ (p₁ : p a) (p₂ : p b), q b p₂ → q a p₁) (h₁ : p a) : q b h₂ → q a h₁ :=
by blast

example (a b : nat) (h₂ : p b) (h₁ : p a) (H : ∀ (p₁ : p a) (p₂ : p b), q b p₂ → q a p₁) : q b h₂ → q a h₁ :=
by blast

example (a b : nat) (h₁ : p a) (H : ∀ (p₁ : p a) (p₂ : p b), q b p₂ → q a p₁) (h₂ : p b) : q b h₂ → q a h₁ :=
by blast
