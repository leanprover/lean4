import types.eq
open eq

variables {A : Type} {a1 a2 a3 : A}
definition my_transport_eq_l (p : a1 = a2) (q : a1 = a3)
    : transport (λx, x = a3) p q = p⁻¹ ⬝ q :=
begin
  rewrite transport_eq_l,
end
