-- HoTT
import types.sigma
open sigma sigma.ops eq
definition dpair_sigma_eq {A : Type} {B : A → Type} {u v : Σa, B a} (p : u.1 = v.1) (q : u.2 =[p] v.2)
  : ⟨(sigma_eq p q)..1, (sigma_eq p q)..2⟩ = ⟨p, q⟩ :=
begin
  induction u with u₁ u₂,
  induction v with v₁ v₂,
  esimp at q,
  induction q, -- Should fail here since index p depends one index v₂
  reflexivity
end
