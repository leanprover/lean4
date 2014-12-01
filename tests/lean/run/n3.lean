prelude
definition Prop : Type.{1} := Type.{0}
constant N : Type.{1}
constant and : Prop → Prop → Prop
infixr `∧`:35 := and
constant le : N → N → Prop
constant lt : N → N → Prop
constant f : N → N
constant add : N → N → N
infixl `+`:65 := add
precedence `≤`:50
precedence `<`:50
infixl ≤ := le
infixl < := lt
notation A ≤ B:prev ≤ C:prev := A ≤ B ∧ B ≤ C
notation A ≤ B:prev < C:prev := A ≤ B ∧ B < C
notation A < B:prev ≤ C:prev := A < B ∧ B ≤ C
constants a b c d e : N
check a ≤ b ≤ f c + b ∧ a < b
check a ≤ d
check a < b ≤ c
check a ≤ b < c
check a < b
