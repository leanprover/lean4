structure Foo where num : Nat deriving DecidableEq

namespace Foo

instance : OfNat Foo n := ⟨⟨n⟩⟩

/-! # Example 1 -/

@[irreducible] def mul (a b : Foo) : Foo :=
  let d := Nat.gcd a.num 1
  ⟨(a.num.div d) * (b.num.div d)⟩

-- should fail fast; exact heartbeat count at time of writing is 31
set_option maxHeartbeats 310
/--
error: tactic 'decide' failed for proposition
  ((mul 4 1).mul 1).mul 1 = 4
since its 'Decidable' instance
  instDecidableEqFoo (((mul 4 1).mul 1).mul 1) 4
did not reduce to 'isTrue' or 'isFalse'.

After unfolding the instances 'decEqFoo✝', 'instDecidableEqFoo', 'instDecidableEqNat', 'withPtrEqDecEq' and 'Nat.decEq', reduction got stuck at the 'Decidable' instance
  match h :
    withPtrEq (((mul 4 1).mul 1).mul 1) 4
      (fun x =>
        toBoolUsing
          ((fun x =>
              match ((mul 4 1).mul 1).mul 1, 4 with
              | { num := a }, { num := b } => if h : a = b then h ▸ isTrue ⋯ else isFalse ⋯)
            ()))
      ⋯ with
  | true => isTrue ⋯
  | false => isFalse ⋯
-/
#guard_msgs in
example : ((Foo.mul 4 1).mul 1).mul 1 = 4 := by decide

/-! # Example 2 -/

@[irreducible] def add (a b : Foo) : Foo := ⟨a.num * b.num⟩

-- should not succeed (and fail fast); exact heartbeat count at time of writing is 21
/--
error: tactic 'decide' failed for proposition
  ((add 4 1).add 1).add 1 = 4
since its 'Decidable' instance
  instDecidableEqFoo (((add 4 1).add 1).add 1) 4
did not reduce to 'isTrue' or 'isFalse'.

After unfolding the instances 'decEqFoo✝', 'instDecidableEqFoo', 'instDecidableEqNat', 'withPtrEqDecEq' and 'Nat.decEq', reduction got stuck at the 'Decidable' instance
  match h :
    withPtrEq (((add 4 1).add 1).add 1) 4
      (fun x =>
        toBoolUsing
          ((fun x =>
              match ((add 4 1).add 1).add 1, 4 with
              | { num := a }, { num := b } => if h : a = b then h ▸ isTrue ⋯ else isFalse ⋯)
            ()))
      ⋯ with
  | true => isTrue ⋯
  | false => isFalse ⋯
-/
#guard_msgs in
example : ((Foo.add 4 1).add 1).add 1 = 4 := by decide
