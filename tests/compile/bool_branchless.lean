module

/-! Regression test for #10835: basic `Bool` operations compile through scalar helpers. -/

@[noinline]
def notValue (b : Bool) : Bool :=
  !b

@[noinline]
def xorValue (a b : Bool) : Bool :=
  a ^^ b

@[noinline]
def natValue (b : Bool) : Nat :=
  b.toNat

public def main : IO Unit := do
  IO.println (notValue true)
  IO.println (notValue false)
  IO.println (xorValue false false)
  IO.println (xorValue false true)
  IO.println (xorValue true false)
  IO.println (xorValue true true)
  IO.println (natValue true)
  IO.println (natValue false)
