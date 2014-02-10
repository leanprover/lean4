theorem or_imp (p q : Bool) : (p ∨ q) ↔ (¬ p → q)
:= subst (symm (imp_or (¬ p) q)) (not_not_eq p)

