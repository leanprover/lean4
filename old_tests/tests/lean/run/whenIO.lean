import system.io
open io

def iowhen (b : bool) (a : io unit) : io unit :=
if b = tt then a else return ()

#eval iowhen tt (put_str "hello\n")
#eval iowhen ff (put_str "error\n")
