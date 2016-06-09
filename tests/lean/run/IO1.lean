import system.IO data.list
open list

-- set_option pp.all true

definition main : IO unit :=
  do l₁ ← get_line,
     l₂ ← get_line,
     put_str (l₂ ++ l₁)

-- vm_eval main
-- set_option trace.compiler.code_gen true

vm_eval put_str "hello\n"

print "************************"

definition aux (n : nat) : IO unit :=
  do put_str "========\nvalue: ",
     put_nat n,
     put_str "\n========\n"

vm_eval aux 20

print "************************"

definition repeat : nat → (nat → IO unit) → IO unit
| 0     a := return ()
| (n+1) a := do a n, repeat n a

vm_eval repeat 10 aux

print "************************"

definition execute : list (IO unit) → IO unit
| []      := return ()
| (x::xs) := do x, execute xs

vm_eval repeat 10 (λ i, execute [aux i, put_str "hello\n"])

print "************************"

vm_eval
  do n ← return 10,
     put_str "value: ",
     put_nat n,
     put_str "\n",
     put_nat (n+2),
     put_str "\n----------\n"

print "************************"
