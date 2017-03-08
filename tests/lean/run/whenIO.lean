import system.io
open io
def iowhen (b : bool) (a : io unit) : io unit :=
if b = tt then a else return ()

vm_eval iowhen tt (put_str "hello\n")
vm_eval iowhen ff (put_str "error\n")
