import Lean

elab tk:"#R[" ts:term,* "]" : term => do
  let ts : Array Lean.Syntax := ts
  let es ← ts.mapM fun stx => Lean.Elab.Term.elabTerm stx none
  if h : 0 < es.size then
    return (Lean.RArray.toExpr (← Lean.Meta.inferType es[0]!) id (Lean.RArray.ofArray es h))
  else
    throwErrorAt tk "RArray cannot be empty"

open Lean.Grind.Offset

macro "C[" "#" x:term:max " ≤ " "#" y:term:max "]" : term => `({ x := $x, y := $y : Cnstr })
macro "C[" "#" x:term:max " + " k:term:max " ≤ " "#" y:term:max "]" : term => `({ x := $x, y := $y, k := $k : Cnstr })
macro "C[" "#" x:term:max " ≤ " "#"y:term:max " + " k:term:max "]" : term => `({ x := $x, y := $y, k := $k, l := false : Cnstr })

example (x y z : Nat) : x + 2 ≤ y → y ≤ z → z + 1 ≤ x → False :=
  Cnstrs.unsat #R[x, y, z] [
    C[ #0 + 2 ≤ #1 ],
    C[ #1 ≤ #2 ],
    C[ #2 + 1 ≤ #0 ]
  ] rfl

example (x y z w : Nat) : x + 2 ≤ y → y ≤ z → z ≤ w + 7 → x ≤ w + 5 :=
  Cnstrs.imp #R[x, y, z, w] [
    C[ #0 + 2 ≤ #1 ],
    C[ #1 ≤ #2 ],
    C[ #2 ≤ #3 + 7]
  ]
  C[ #0 ≤ #3 + 5 ]
  rfl
