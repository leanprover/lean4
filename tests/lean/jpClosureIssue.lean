@[inline] def f (b : Bool) : IO Nat :=
  match b with
  | true  => return 0
  | false => return 1

@[noinline] def print (x : Nat) : IO Unit :=
  IO.println x

set_option trace.Compiler.saveMono true
def foo (b : Bool) : IO Unit :=
  bind (f b) fun x => print x
