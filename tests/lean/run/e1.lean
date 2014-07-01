definition Bool [inline] : Type.{1} := Type.{0}
variable eq : forall {A : Type}, A → A → Bool
variable N : Type.{1}
variables a b c : N
infix `=`:50 := eq
check a = b

variable f : Bool → N → N
variable g : N → N → N
precedence `+`:50
infixl + := f
infixl + := g
check a + b + c
variable p : Bool
check p + a + b + c
