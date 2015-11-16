/- Basic pi congruence -/
import logic.connectives logic.quantifiers

namespace pi_congr1
constants (p1 q1 p2 q2 p3 q3 : Prop) (H1 : p1 ↔ q1) (H2 : p2 ↔ q2) (H3 : p3 ↔ q3)
namespace tst
attribute congr_forall [congr]
attribute congr_imp    [congr]
attribute H1 [simp]
attribute H2 [simp]
attribute H3 [simp]
end tst

#simplify iff tst 1 p1 -- Broken?
#simplify iff tst 1 p1 →  p2
#simplify iff tst 1 p1 →  p2 → p3

end pi_congr1

namespace pi_congr2
universe l
constants (T : Type.{l}) (P Q : T → Prop) (H : ∀ (x : T), P x ↔ Q x)
namespace tst
attribute H [simp]
end tst
constant (x : T)

#simplify iff tst 1 (∀ (x : T), P x)


end pi_congr2
