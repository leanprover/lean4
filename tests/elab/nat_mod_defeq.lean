/-!
This tests that `0 : Fin (n + 1)` unfolds to `0 : Nat`, which is a property kept for backwards
compatibility with mathlib in Lean 3.

Some Zulip discussion is available
[here](https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Nat.2Emod.200.20n.20.3D.200.20no.20longer.20true.20by.20rfl/near/319683008).
-/

example (n : Nat) : 0 % n = 0 := rfl
example (n : Nat) : (0 : Fin (n + 1)).val = 0 := rfl
