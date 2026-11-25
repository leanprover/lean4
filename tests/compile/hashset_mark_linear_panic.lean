import Std.Data.HashSet

/-!
Tests that inserting into a hash set marked by `HashSet.markLinear` while it is shared aborts
instead of silently copying the bucket array.
-/

def bad (n : Nat) : Nat :=
  let s := (Std.HashSet.emptyWithCapacity n).markLinear
  let s' := s.insert 0
  -- The lookup has to touch the bucket array; reading `s.size` instead would be constant-folded
  -- away, leaving the insertion with the only reference to the array.
  s'.size + (if s.contains 0 then 1 else 0)

def main : IO Unit :=
  IO.println (bad 16)
