import system.io
open io
set_option trace.compiler.code_gen true

definition main : io unit :=
do { n ← return (10:nat),
     if n = (11:nat) then
       put 1
     else
       put 2 }

vm_eval main
