constant f (a b : nat) : a > b → nat
constant g : nat → nat
open tactic

example (a₁ a₂ b₁ b₂ c d : nat)
        (H₁ : a₁ > b₁)
        (H₂ : a₂ > b₂) :
        a₁ = c → a₂ = c →
        b₁ = d → d  = b₂ →
        g (g (f a₁ b₁ H₁)) = g (g (f a₂ b₂ H₂)) :=
by cc

example (a₁ a₂ b₁ b₂ c d : nat) :
        a₁ = c → a₂ = c →
        b₁ = d → d  = b₂ →
        a₁ + b₁ + a₁ = a₂ + b₂ + c :=
by cc

example (a b c : Prop) : (a ↔ b) → ((a ∧ (c ∨ b)) ↔ (b ∧ (c ∨ a))) :=
by cc

example (a b c d : Prop)
     [d₁ : decidable a] [d₂ : decidable b] [d₃ : decidable c] [d₄ : decidable d]
   : (a ↔ b) → (c ↔ d) → ((if (a ∧ c) then true else false) ↔ (if (b ∧ d) then true else false)) :=
by cc

example (a b c d : Prop) (x y z : nat)
     [d₁ : decidable a] [d₂ : decidable b] [d₃ : decidable c] [d₄ : decidable d]
   : (a ↔ b) → (c ↔ d) → x = y → ((if (a ∧ c ∧ a) then x else y) = (if (b ∧ d ∧ b) then y else x)) :=
by cc
