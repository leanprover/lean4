import init.lean.evalconst
open Lean

def someVal := 100
def someVal2 : UInt64 := 302
def someVal3 : Bool := true
def add10 (n : Nat) := n+10
def mul10 (n : Nat) := n*10
def inc (n : Nat) := n+1

unsafe def evalNatFn (fName : Name) (n : Nat) : IO Unit :=
do f ← evalConst (Nat → Nat) fName,
   IO.println (f n)

unsafe def evalVal (α : Type) [Inhabited α] [ToString α] (n : Name) : IO Unit :=
do v ← evalConst α n,
   IO.println v

unsafe def main (xs : List String) : IO Unit :=
do let x := xs.head.toNat,
   sortConstTable, -- we don't sort the constant table by default in standalone applications
   evalNatFn `add10 x,
   evalNatFn `mul10 x,
   evalNatFn `inc x,
   evalVal Nat `someVal,
   evalVal UInt64 `someVal2,
   evalVal Bool `someVal3,
   pure ()
