import system.io
open list
open io

-- set_option pp.all true

definition main : io unit :=
  do l₁ ← get_line,
     l₂ ← get_line,
     put_str (l₂ ++ l₁)

-- vm_eval main
-- set_option trace.compiler.code_gen true

#eval put_str "hello\n"

#print "************************"

definition aux (n : nat) : io unit :=
  do put_str "========\nvalue: ",
     print n,
     put_str "\n========\n"

#eval aux 20

#print "************************"

definition repeat : nat → (nat → io unit) → io unit
| 0     a := return ()
| (n+1) a := do a n, repeat n a

#eval repeat 10 aux

#print "************************"

definition execute : list (io unit) → io unit
| []      := return ()
| (x::xs) := do x, execute xs

#eval repeat 10 (λ i, execute [aux i, put_str "hello\n"])

#print "************************"

#eval
  do n ← return 10,
     put_str "value: ",
     print n,
     put_str "\n",
     print (n+2),
     put_str "\n----------\n"

#print "************************"
