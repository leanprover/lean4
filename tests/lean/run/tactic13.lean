import standard
using tactic

theorem tst (a b : Prop) (H : ¬ a ∨ ¬ b) (Hb : b) : ¬ a ∧ b :=
begin
  apply and_intro,
  apply not_intro,
  assume Ha, or_elim H
    (assume Hna, absurd Ha Hna)
    (assume Hnb, absurd Hb Hnb),
  assumption
end