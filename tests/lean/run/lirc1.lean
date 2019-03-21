import init.Lean.Ir.lirc
open Lean.Ir

def comp (s : String) : Eio Unit :=
match lirc s with
| Except.ok r    := IO.print r
| Except.error e := IO.print "Error: " *> IO.print e

def PRG1 := "
[makeMyPair] external foo (a : object) (b : object) : object

def bla (g : object) (a : object) (z : UInt32) : object :=
main:
  a' := call foo a a;
  c d := call boo a;
  r   := cnstr 0 2 0;
  w   := call f a a a a a a a a a a a a a a a a a a;
  w'  := apply g a a a;
  w''  := apply g a a a a a a a a a a a a a a a a a a;
  one : UInt32 := 1;
  z' : UInt32 := add z one;
  h := closure foo a;
  h' := closure f a a a;
  n : object := 1000;
  n' : object := 10000000000000000000;
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
