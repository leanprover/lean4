/-!
Tests `ByteArray.replicate` and `ByteArray.shrink`, including shrinking a shared array.
-/

@[noinline] def shrink (a : ByteArray) (n : Nat) : ByteArray := a.shrink n

def main : IO Unit := do
  IO.println (ByteArray.replicate 5 7)
  IO.println (ByteArray.replicate 0 7)
  let a := ByteArray.mk #[1, 2, 3, 4, 5]
  IO.println (shrink (ByteArray.mk #[1, 2, 3, 4, 5]) 2)
  IO.println (shrink (ByteArray.mk #[1, 2, 3, 4, 5]) 9)
  IO.println (shrink (ByteArray.mk #[1, 2, 3, 4, 5]) 5)
  -- `a` is shared, so this must copy
  IO.println s!"{shrink a 3} {a}"
