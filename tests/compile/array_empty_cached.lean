module

import Init.Data.Array.Basic
import Init.Util

/-!
Tests that zero-capacity arrays reuse the runtime's cached empty array.
-/

set_option compiler.extract_closed false

@[noinline] def empty : Unit → Array Nat := fun _ => Array.empty

@[noinline] def emptyLiteral : Unit → Array Nat := fun _ => #[]

@[noinline] def emptyWithCapacity : Unit → Array Nat := fun _ => Array.emptyWithCapacity 0

@[noinline] def mkEmpty : Unit → Array Nat := fun _ => Array.mkEmpty 0

@[noinline] def emptyWithPositiveCapacity : Unit → Array Nat := fun _ => Array.emptyWithCapacity 1

public unsafe def main : IO Unit := do
  let xs := empty ()
  IO.println (ptrEq xs (emptyLiteral ()))
  IO.println (ptrEq xs (emptyWithCapacity ()))
  IO.println (ptrEq xs (mkEmpty ()))
  IO.println (isExclusiveUnsafe (emptyWithPositiveCapacity ()))
  let ys := xs.push 42
  IO.println (xs.isEmpty && ys == #[42])
