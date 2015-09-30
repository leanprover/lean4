prelude constant N : Type.{1}
definition B : Type.{1} := Type.{0}
constant ite : B → N → N → N
constant and : B → B → B
constant f : N → N
constant p : B
constant q : B
constant x : N
constant y : N
constant z : N
infixr ` ∧ `:25 := and
notation `if` c `then` t:45 `else` e:45 := ite c t e
check if p ∧ q then f x else y
check if p ∧ q then q else y
constant list : Type.{1}
constant nil : list
constant cons : N → list → list
-- Non empty lists
notation `[` l:(foldr `, ` (h t, cons h t) nil) `]` := l
check [x, y, z, x, y, y]
check [x]
notation `[` `]` := nil
check []
