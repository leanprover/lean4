import standard
using tactic

theorem tst (a b : Bool) (H : ¬ a ∨ ¬ b) (Hb : b) : ¬ a ∧ b :=
proof
  apply and_intro,
  apply not_intro,
  assume Ha, or_elim H
    (assume Hna, absurd Ha Hna)
    (assume Hnb, absurd Hb Hnb),
  assumption
qed