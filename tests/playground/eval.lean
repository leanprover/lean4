import init.lean.name
open Lean

abbrev ConstantTable (α : Type) := HashMap Name α

def mkSimpleFnTable : IO (IO.Ref (ConstantTable (Nat → Nat))) :=
IO.mkRef {}

@[init mkSimpleFnTable]
constant simpleFnTable : IO.Ref (ConstantTable (Nat → Nat)) := default _

def registerSimpleFn (n : Name) (fn : Nat → Nat) : IO Unit :=
do ini ← IO.initializing,
   unless ini (throw "we should only register functions during initialization"),
   simpleFnTable.modify (λ m, m.insert n fn)

def add10 (n : Nat) := n+10
def mul10 (n : Nat) := n*10
def inc (n : Nat) := n+1

@[init] def regAdd10 : IO Unit := registerSimpleFn `add10 add10
@[init] def regMul10 : IO Unit := registerSimpleFn `mul10 mul10
@[init] def regInc   : IO Unit := registerSimpleFn `inc inc

def eval (fName : Name) (n : Nat) : IO Nat :=
do m ← simpleFnTable.get,
   match m.find fName with
   | some f := pure $ f n
   | none   := throw (IO.userError "unknown function")

def main (xs : List String) : IO Unit :=
do [f, x] ← pure xs | throw "invalid number of arguments",
   r ← eval (mkSimpleName f) x.toNat,
   IO.println r,
   pure ()
