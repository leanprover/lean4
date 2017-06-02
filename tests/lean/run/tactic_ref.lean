open tactic

meta def tst1 (n : nat) : tactic nat :=
using_new_ref n $ λ r, do
  v ← read_ref r,
  trace v,
  write_ref r (v*2),
  v ← read_ref r,
  trace v,
  return v

example : true :=
by do
  v ← tst1 10,
  guard (v = 20),
  constructor

meta def tst2 : tactic nat :=
do r ← using_new_ref 0 $ λ r, do {
           return r
       },
   read_ref r -- Should produce an exception, the reference is not valid anymore

run_cmd fail_if_success $ tst2

meta def tst3 (n : nat) : tactic nat :=
using_new_ref n $ λ r,
  (write_ref r (n+10) >> failed) -- The state should be restored during backtracking
  <|>
  (read_ref r)

example : true :=
by do
  v ← tst3 10,
  guard (v = 10),
  constructor
