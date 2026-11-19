partial def frob : Nat → Nat | i =>
if i > 10 then frob 5 else frob (i-1)
