theorem symm_iff (p q : Bool) (H : p ↔ q) : (q ↔ p)
:= symm H

theorem or_imp (p q : Bool) : (p ∨ q) ↔ (¬ p → q)
:= let H1 := symm_iff _ _ (imp_or (¬ p) q) in
   let H2 := not_not_eq p in
   let H3 := subst H1 H2 in
   H3
