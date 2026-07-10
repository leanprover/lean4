module

/-!
Tests wasm32 large natural literals and bignum runtime operations.
-/

@[noinline] def large (x : Nat) : Nat :=
  x + 4294967296

@[export lean_wasm_big_nat]
def bigNat (x : UInt32) : UInt32 :=
  (large x.toNat % 97).toUInt32
