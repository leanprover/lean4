open nat
set_option blast.strategy "cc"

constant f (a b : nat) : a > b → nat
constant g : nat → nat

definition tst
        (a₁ a₂ b₁ b₂ c d : nat)
        (H₁ : a₁ > b₁)
        (H₂ : a₂ > b₂) :
        a₁ = c → a₂ = c →
        b₁ = d → d  = b₂ →
        g (g (f a₁ b₁ H₁)) = g (g (f a₂ b₂ H₂)) :=
by blast

print tst
