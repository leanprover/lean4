import system.io
import init.lean.ir.lirc
open lean.ir

def comp (s : string) : io unit :=
match lirc s with
| except.ok r    := io.print r
| except.error e := io.print "Error: " >> io.print e

def PRG1 := "
[lean::mk_pair] external foo (a : object) (b : object) : object

def bla (a : object) : object :=
main:
  r := call foo a a;
  ret r;
"

#eval comp PRG1
