universes u

def a : Array ((Nat × Nat) × Bool) := #[]
def b : Array Nat := #[]

structure Foo :=
(x : Array ((Nat × Nat) × Bool) := #[])
(y : Nat := 0)

new_frontend

#check (b).modifyOp (idx := 1) (fun s => 2)

#check { [1] := 2, .. b }

#check { [1].fst.2 := 1, .. a }

def foo : Foo := {}

#check { x[1].2 := true, .. foo }
#check { x[1].fst.snd := 1, .. foo }
#check { x[1].1.fst := 1, .. foo }
