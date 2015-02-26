prelude
definition Prop : Type.{1} := Type.{0}

inductive or (A B : Prop) : Prop :=
| intro_left  : A → or A B
| intro_right : B → or A B

check or
check or.intro_left
check or.rec
