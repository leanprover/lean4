def foo (a : array nat) : array nat :=
let a := a.push 0 in
let a := a.push 1 in
let a := a.push 2 in
let a := a.push 3 in
a

def main : io uint32 :=
do
 let a : array nat := array.nil,
 io.println (to_string a),
 io.println (to_string a.sz),
 let a := foo a,
 io.println (to_string a),
 let a := a.map (+10),
 io.println (to_string a),
 io.println (to_string a.sz),
 let a1 := a.pop,
 let a2 := a.push 100,
 io.println (to_string a1),
 io.println (to_string a2),
 let a2 := a.pop,
 io.println a2,
 pure 0
