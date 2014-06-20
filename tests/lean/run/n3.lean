definition Bool [inline] : Type.{1} := Type.{0}
variable N : Type.{1}
variable and : Bool → Bool → Bool
infixr `∧` 35 := and
variable le : N → N → Bool
variable lt : N → N → Bool
precedence `≤`:50
precedence `<`:50
infixl ≤ := le
infixl < := lt
notation A ≤ B ≤ C := A ≤ B ∧ B ≤ C
notation A ≤ B < C := A ≤ B ∧ B < C
notation A < B ≤ C := A < B ∧ B ≤ C
variables a b c d e : N
check a ≤ b ≤ c
check a ≤ d
check a < b ≤ c
check a ≤ b < c
check a < b
