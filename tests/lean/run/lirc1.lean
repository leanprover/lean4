import system.io
import init.lean.ir.lirc
open lean.ir

def comp (s : string) : io unit :=
match lirc s with
| except.ok r    := io.print r
| except.error e := io.print "Error: " >> io.print e

def PRG1 := "
[lean::mk_pair] external foo (a : object) (b : object) : object

def bla (g : object) (a : object) (z : uint32) : object :=
main:
  a' := call foo a a;
  c d := call boo a;
  r   := cnstr 0 2 0;
  w   := call f a a a a a a a a a a a a a a a a a a;
  w'  := apply g a a a;
  w''  := apply g a a a a a a a a a a a a a a a a a a;
  one : uint32 := 1;
  z' : uint32 := add z one;
  h := closure foo a;
  h' := closure f a a a;
  set r 0 a';
  set r 1 d;
  ret r;

def f (a1 : object) (a2 : object) (a3 : object) (a4 : object) (a5 : object)
      (a6 : object) (a7 : object) (a8 : object) (a9 : object) (a10 : object)
      (a11 : object) (a12 : object) (a13 : object) (a14 : object) (a15 : object)
      (a16 : object) (a17 : object) (a18 : object) : object :=
main:
  ret a16;

def boo (a : object) : object object :=
main:
  ret a a;
"

#eval comp PRG1
