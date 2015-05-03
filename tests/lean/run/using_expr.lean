example (p q : Prop) (H : p ∧ q) : p ∧ q ∧ p :=
have Hp : p, from and.elim_left H,
have Hq : q, from and.elim_right H,
using Hp Hq,
begin
  apply and.intro, assumption,
  apply and.intro, repeat assumption
end
