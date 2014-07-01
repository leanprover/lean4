variable N : Type.{1}
definition B : Type.{1} := Type.{0}
variable ite : B → N → N → N
variable and : B → B → B
variable f : N → N
variable p : B
variable q : B
variable x : N
variable y : N
variable z : N
infixr `∧`:25 := and
notation `if` c `then` t `else` e := ite c t e
check if p ∧ q then f x else y
check if p ∧ q then q else y
variable list : Type.{1}
variable nil : list
variable cons : N → list → list
-- Non empty lists
notation `[` l:(foldr `,` (h t, cons h t) nil) `]` := l
check [x, y, z, x, y, y]
check [x]
notation `[` `]` := nil
check []
