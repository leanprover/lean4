import system.io
open io state_t

@[reducible] def my_io := state_t nat io

instance lift_io {α} : has_coe (io α) (my_io α) :=
⟨state_t.lift⟩

def tst : my_io unit :=
do x ← get,
   println x,
   put (x+10),
   y ← get,
   println y,
   put_str "end of program"

#eval tst.run 5
