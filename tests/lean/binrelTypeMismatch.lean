/-!
# Testing that type mismatch errors for binary operations are localized to the LHS or RHS

Before #3442, the error was placed on the entire expression than just the RHS.
-/

/-!
When there's no max type, the ensureHasType failure is localized to the RHS.
-/
#check true = ()

/-!
When there's no max type, toBoolIfNecessary error is localized to LHS.
-/
#check ∀ (p : Prop), p == ()

/-!
When there's no max type, toBoolIfNecessary error is localized to RHS.
-/
#check ∀ (p : Prop), () == p
