/-!
# Tests of the metaprogram to prove types are inhabited for `partial`
-/

/-!
Example: callbacks that depend on some inhabited arguments.
-/
partial def callback1 (k : Array Nat → α) : α := callback1 k

partial def callback2 (k : Array Nat → IO α) : IO α := callback2 k

partial def callback3 (k : Array Nat → α) : IO α := callback3 k

/-!
Example: some arguments might depend on results of other functions.
-/
partial def callback4 (k : Array α → β → α) (f : Unit → β) : IO α := callback4 k f
