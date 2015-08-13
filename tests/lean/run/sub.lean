import data.nat
open nat

notation `{` binders:55 `|` r:(scoped P, subtype P) `}` := r
check { x : nat | x > 0 }
check { (x : nat → nat) | true }
