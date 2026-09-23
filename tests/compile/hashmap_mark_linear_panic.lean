import Std.Data.HashMap

/-!
Tests that inserting into a hash map marked by `HashMap.markLinear` while it is shared aborts
instead of silently copying the bucket array.
-/

def bad (n : Nat) : Nat :=
  let m := (Std.HashMap.emptyWithCapacity n).markLinear
  let m' := m.insert 0 0
  -- The lookup has to touch the bucket array; reading `m.size` instead would be constant-folded
  -- away, leaving the insertion with the only reference to the array.
  m'.size + (if m.contains 0 then 1 else 0)

def main : IO Unit :=
  IO.println (bad 16)
