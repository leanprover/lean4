open tactic

run_command tactic.trace "hello world"

run_command do
 N ← to_expr `(nat),
 v ← to_expr `(10),
 add_decl (declaration.defn `val10 [] N v reducibility_hints.opaque tt)

vm_eval val10

example : val10 = 10 := rfl

meta definition mk_defs : nat → command
| 0     := skip
| (n+1) := do
   N ← to_expr `(nat),
   v ← expr_of_nat n,
   add_decl (declaration.defn (name.append_after `val n) [] N v reducibility_hints.opaque tt),
   mk_defs n

run_command mk_defs 10

example : val_1 = 1 := rfl
example : val_2 = 2 := rfl
example : val_3 = 3 := rfl
example : val_4 = 4 := rfl
example : val_5 = 5 := rfl
example : val_6 = 6 := rfl
example : val_7 = 7 := rfl
example : val_8 = 8 := rfl
example : val_9 = 9 := rfl
