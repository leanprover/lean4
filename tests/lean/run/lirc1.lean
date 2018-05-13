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

def f (a1 : object) (a2 : object) (a3 : object) (a4 : object) (a5 : object)
      (a6 : object) (a7 : object) (a8 : object) (a9 : object) (a10 : object)
      (a11 : object) (a12 : object) (a13 : object) (a14 : object) (a15 : object)
      (a16 : object) (a17 : object) (a18 : object) : object :=
main:
  ret a16;
"

#eval comp PRG1
