import logic
open tactic

definition basic_tac : tactic
:= repeat (apply @and.intro | assumption)

set_begin_end_tactic basic_tac -- basic_tac is automatically applied to each element of a proof-qed block

theorem tst (a b : Prop) (H : ¬ a ∨ ¬ b) (Hb : b) : ¬ a ∧ b :=
begin
  assume Ha, or.elim H
    (assume Hna, @absurd _ false Ha Hna)
    (assume Hnb, @absurd _ false Hb Hnb)
end
