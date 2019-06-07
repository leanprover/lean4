import init.lean.evalconst
open Lean

def add10 (n : Nat) := n+10
def mul10 (n : Nat) := n*10
def inc (n : Nat) := n+1

unsafe def eval (fName : Name) (n : Nat) : IO Unit :=
do f ← evalConst (Nat → Nat) fName,
   IO.println (f n)

unsafe def main (xs : List String) : IO Unit :=
do let x := xs.head.toNat,
   sortConstTable, -- we don't sort the constant table by default in standalone applications
   eval `add10 x,
   eval `mul10 x,
   eval `inc x,
   pure ()
