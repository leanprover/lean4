structure Foo where num : Nat deriving DecidableEq

namespace Foo

instance : OfNat Foo n := ⟨⟨n⟩⟩

/-! # Example 1 -/

@[irreducible] def mul (a b : Foo) : Foo :=
  let d := Nat.gcd a.num 1
  ⟨(a.num.div d) * (b.num.div d)⟩

-- should fail fast; exact heartbeat count at time of writing is 31
set_option maxHeartbeats 310
example : ((Foo.mul 4 1).mul 1).mul 1 = 4 := by decide

/-! # Example 2 -/

@[irreducible] def add (a b : Foo) : Foo := ⟨a.num * b.num⟩

-- should not succeed (and fail fast); exact heartbeat count at time of writing is 21
example : ((Foo.add 4 1).add 1).add 1 = 4 := by decide
