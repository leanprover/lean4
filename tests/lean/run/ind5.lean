prelude
definition Prop : Type.{1} := Type.{0}

inductive or (A B : Prop) : Prop
| intro_left  : A → or
| intro_right : B → or

#check or
#check or.intro_left
#check or.rec
