module

@[noinline]
unsafe def smallNat (n : Nat) : Bool := isExclusiveUnsafe n

@[noinline]
unsafe def scalarCtor (_n : Nat) : Bool := isExclusiveUnsafe (none : Option Nat)

inductive Enum where
  | a
  | b
  | c

@[noinline]
unsafe def enumCtor (_n : Nat) : Bool := isExclusiveUnsafe Enum.a

@[noinline]
unsafe def unit (_n : Nat) : Bool := isExclusiveUnsafe ()

public unsafe def main (args : List String) : IO Unit := do
  IO.println <| smallNat args.length
  IO.println <| scalarCtor args.length
  IO.println <| enumCtor args.length
  IO.println <| unit args.length
