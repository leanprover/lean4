open eq eq.ops

variable {A : Type}

definition trans : Π {x y z : A} (p : x = y) (q : y = z), x = z
| trans (refl a) (refl a) := refl a

set_option pp.purify_locals false

definition con_inv_cancel_left : Π {x y z : A} (p : x = y) (q : x = z), p ⬝ (p⁻¹ ⬝ q) = q
| con_inv_cancel_left (refl a) (refl a) := refl (refl a)

definition inv_con_cancel_left : Π {x y z : A} (p : x = y) (q : y = z), p⁻¹ ⬝ (p ⬝ q) = q
| inv_con_cancel_left (refl a) (refl a) := refl (refl a)
