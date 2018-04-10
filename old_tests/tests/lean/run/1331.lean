def is_space : char → Prop
| ' '    := true
| '\x09' := true -- \t
| '\n'   := true
| '\x0d' := true -- \r
| _      := false

instance is_space.decidable_pred : decidable_pred is_space :=
begin delta is_space, apply_instance end

def f (a : nat) : nat :=
a + 2

open tactic

lemma flemma : f 0 = 2 :=
begin
  delta f,
  guard_target 0 + 2 = 2,
  reflexivity
end
