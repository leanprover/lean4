def I : nat → nat := λ x, x

meta def buggy : tactic unit :=
do let t : expr := expr.app (expr.const `I []) (expr.const `bool.tt []),
   tactic.exact t

def t (y : nat) : nat :=
let x := 1 + y in
by buggy
