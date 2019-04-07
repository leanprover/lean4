def foo (a : Array Nat) : Array Nat :=
let a := a.push 0 in
let a := a.push 1 in
let a := a.push 2 in
let a := a.push 3 in
a

def main : IO UInt32 :=
do
 let a : Array Nat := Array.empty,
 IO.println (toString a),
 IO.println (toString a.sz),
 let a := foo a,
 IO.println (toString a),
 let a := a.hmap (+10),
 IO.println (toString a),
 IO.println (toString a.sz),
 let a1 := a.pop,
 let a2 := a.push 100,
 IO.println (toString a1),
 IO.println (toString a2),
 let a2 := a.pop,
 IO.println a2,
 IO.println $ (([1, 2, 3, 4].toArray).hmap (+2)).map toString,
 pure 0
