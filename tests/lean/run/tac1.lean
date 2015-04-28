import logic
open tactic

notation `(` h `|` r:(foldl `|` (e r, tactic.or_else r e) h) `)` := r
infixl `;`:15 := tactic.and_then

definition mytac := apply @and.intro; apply @eq.refl

check @mytac
