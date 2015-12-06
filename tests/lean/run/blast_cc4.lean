open nat
set_option blast.strategy "cc"

definition tst
        (a₁ a₂ b₁ b₂ c d : nat) :
        a₁ = c → a₂ = c →
        b₁ = d → d  = b₂ →
        a₁ + b₁ + a₁ = a₂ + b₂ + c :=
by blast

print tst
