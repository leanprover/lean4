import logic
open tactic

notation `(` h `|` r:(foldl `|` (e r, tactic.or_else r e) h) `)` := r
infixl `;`:15 := tactic.and_then


theorem T (a b c d : Prop) (Ha : a) (Hb : b) (Hc : c) (Hd : d) : a ∧ b ∧ c ∧ d
:= by fixpoint (λ f, (apply and.intro; f | assumption; f | id))
