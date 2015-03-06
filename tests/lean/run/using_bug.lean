example (p q r : Prop) : p ∧ q ∧ r → q ∧ p :=
assume Hpqr : p ∧ q ∧ r,
have   Hp   : p,     from and.elim_left Hpqr,
have   Hqr  : q ∧ r, from and.elim_right Hpqr,
have   Hq   : q,     from and.elim_left Hqr,
show q ∧ p, using Hp Hq, from
proof
  and.intro Hq Hp
qed
