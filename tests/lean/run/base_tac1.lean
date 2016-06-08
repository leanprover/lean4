open tactic

meta_definition tac [reducible] := base_tactic string

definition v : nat := 10

meta_definition t : tac nat :=
return v

open tactic format

meta_definition t2 : tac nat :=
decorate_ex "executing t2"
  (do n₁ ← t,
      n₂ : nat ← return 3,
      decorate_ex "trying nested" (fail "error" <|> fail "error2"),
      return n₁)

vm_eval t2 "initial"

print "------"

meta_definition main : base_tactic nat nat :=
do n₁ ← read,
   write (n₁ + 1),
   n₂ ← read,
   return n₂

vm_eval main 5
