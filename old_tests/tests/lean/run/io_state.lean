import system.io
open io state_t

@[reducible] def my_io := state_t nat io

instance lift_io {α} : has_coe (io α) (my_io α) :=
⟨state_t.lift⟩

def tst : my_io unit :=
do x ← get,
   print_ln x,
   put (x+10),
   y ← get,
   print_ln y,
   put_str "end of program"

#eval tst.run 5
