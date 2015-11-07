-- Rewriting with (tmp)-local hypotheses
import logic.quantifiers

attribute congr_forall [congr]
attribute congr_imp [congr]

universe l
constants (T : Type.{l}) (P Q : T → Prop) 

set_option simplify.max_steps 50000
constants (x y : T)

#simplify iff 0 x = y →  x = y
#simplify iff 0 T → x = y →  x = y
#simplify iff 0 ∀ z : T, x = z → x = y
#simplify iff 0 ∀ z : T, z = x → x = z
#simplify iff 0 ∀ (z w : T), x = y →  x = y
#simplify iff 0 ∀ (z w : T), x = y →  P x

#simplify iff 0 ∀ (H : ∀ x, P x ↔ Q x), P x
#simplify iff 0 ∀ (p : Prop) (H : ∀ x, P x ↔ Q x) (q : Prop), P x

#simplify iff 0 ∀ (p : Prop) (H : ∀ x, P x ↔ Q x), p ∨ P x
#simplify iff 0 (∀ (x : T), P x ↔ Q x) →  P x
#simplify iff 0 (∀ (x : T), P x ↔ Q x) →  P x
#simplify iff 0 ∀ (x y : T), (∀ (x : T), P x ↔ Q x) →  P x

#simplify iff 0 ∀ (x z : T), x = z → (∀ (w : T), P w ↔ Q w) →  P x


