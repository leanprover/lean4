

structure Foo :=
(flag : Bool   := false)
(x    : UInt16 := 0)
(z    : UInt32 := 0)
(w    : UInt64 := 0)
(h    : USize  := 0)
(xs   : List Nat := [])

set_option trace.compiler.ir.init true

def f (s : Foo) : Foo :=
{ s with x := s.x + 1 }

def g (flag : Bool) : Foo :=
let s : Foo := { x := 10, flag := flag };
f s
