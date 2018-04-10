definition range (lower : nat) (upper : nat) : set nat :=
λ a, lower ≤ a ∧ a ≤ upper

local notation `[` L `, ` U `]` := range L U

variables s : set nat
variables p : nat → nat → Prop


-- #check a ∈ s
set_option pp.binder_types true
#check ∀ b c a ∈ s, a + b + c > 0
-- ∀ (b c a : ℕ), b ∈ s → c ∈ s → a ∈ s → a + b + c > 0 : Prop
#check ∀ a < 5, p a (a+1)
-- ∀ (a : ℕ), a < 5 → p a (a + 1) : Prop
#check ∀ a b ∈ [2, 3], p a b
-- ∀ (a b : ℕ), a ∈ [2, 3] → b ∈ [2, 3] → p a b
