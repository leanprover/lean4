module

/-! EmitZig smoke test covering big-`Nat` arithmetic and width conversions. -/

def work (x y : Nat) : Nat × Nat × Nat × Nat × Nat × Bool × Bool × Bool × UInt32 × UInt64 :=
  let add := x + y
  let sub := add - x
  let mul := sub * y
  let div := mul / (x + 1)
  let mod := mul % (y + 1)
  let eq : Bool := add == sub
  let le : Bool := div ≤ mul
  let lt : Bool := mod < mul
  let pow := Nat.pow div 3
  (add, sub, mul, div, mod, eq, le, lt, UInt32.ofNat pow, UInt64.ofNat pow)

def big1 : Nat := 4294967296 * 4294967296 + 123
def big2 : Nat := 18446744073709551616 + 456

def main : IO Unit := do
  let (add, sub, mul, div, mod, eq, le, lt, u32, u64) := work big1 big2
  IO.println (toString add)
  IO.println (toString sub)
  IO.println (toString mul)
  IO.println (toString div)
  IO.println (toString mod)
  IO.println (toString eq)
  IO.println (toString le)
  IO.println (toString lt)
  IO.println (toString u32.toNat)
  IO.println (toString u64.toNat)
