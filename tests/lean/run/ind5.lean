definition [inline] Bool : Type.{1} := Type.{0}

inductive or (A B : Bool) : Bool :=
| or_intro_left  : A → or A B
| or_intro_right : B → or A B

check or
check or_intro_left
check or_rec