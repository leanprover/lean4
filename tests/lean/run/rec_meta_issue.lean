open tactic

meta def left_right_search (tac := assumption) : tactic unit :=
    tac
<|> (left >> left_right_search)
<|> (right >> left_right_search)

example (p q r : Prop) : r → p ∨ q ∨ r :=
begin intros, left_right_search end

example (a b c : nat) : a = b ∨ b = c ∨ a = a :=
begin left_right_search reflexivity end
