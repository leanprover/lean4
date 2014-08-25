import logic
using tactic

theorem T (a b c d : Prop) (Ha : a) (Hb : b) (Hc : c) (Hd : d) : a ∧ b ∧ c ∧ d
:= by fixpoint (λ f, [apply @and_intro; f | assumption; f | id])
