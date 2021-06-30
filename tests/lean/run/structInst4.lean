universe u

def a : Array ((Nat × Nat) × Bool) := #[]
def b : Array Nat := #[]

structure Foo :=
(x : Array ((Nat × Nat) × Bool) := #[])
(y : Nat := 0)

#check (b).modifyOp (idx := 1) (fun s => 2)

#check { b with [1] := 2 }

#check { a with [1].fst.2 := 1 }

def foo : Foo := {}

#check foo.x[1].1.2

#check { foo with x[1].2 := true }
#check { foo with x[1].fst.snd := 1 }
#check { foo with x[1].1.fst := 1 }

#check { foo with x[1].1.1 := 5 }
#check { foo with x[1].1.2 := 5 }
