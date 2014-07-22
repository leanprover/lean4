definition Prop [inline] : Type.{1} := Type.{0}
variable N : Type.{1}
variable and : Prop → Prop → Prop
infixr `∧`:35 := and
variable le : N → N → Prop
variable lt : N → N → Prop
variable f : N → N
variable add : N → N → N
infixl `+`:65 := add
precedence `≤`:50
precedence `<`:50
infixl ≤ := le
infixl < := lt
notation A ≤ B:prev ≤ C:prev := A ≤ B ∧ B ≤ C
notation A ≤ B:prev < C:prev := A ≤ B ∧ B < C
notation A < B:prev ≤ C:prev := A < B ∧ B ≤ C
variables a b c d e : N
check a ≤ b ≤ f c + b ∧ a < b
check a ≤ d
check a < b ≤ c
check a ≤ b < c
check a < b
