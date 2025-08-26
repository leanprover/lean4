module

public axiom P : Nat → Prop
public axiom P.intro : P n

public inductive AckFuel : (n m : Nat) → Type where
  | step1 : AckFuel 0 m
  | step2 : AckFuel n 1 → AckFuel (n + 1) 0
  | step3 : (∀ m', P m' → AckFuel n m') → AckFuel (n + 1) m → AckFuel (n+1) (m + 1)

namespace Test1
/--
info: Try this:
  termination_by structural x _ x => x
-/
#guard_msgs in
public def ackermann_fuel : (n m : Nat) → (fuel : AckFuel n m) → Nat
| 0, m, .step1 => m+1
| n + 1, 0, .step2 f => ackermann_fuel n 1 f
| n + 1, m + 1, .step3 f1 f2 =>
  ackermann_fuel n (ackermann_fuel (n + 1) m f2) (f1 _ (by exact P.intro))
termination_by?
end Test1

namespace Test2
/--
info: Try this:
  termination_by structural x _ x => x
-/
#guard_msgs in
public def ackermann_fuel : (n m : Nat) → (fuel : AckFuel n m) → Nat
| 0, m, .step1 => m+1
| n + 1, 0, .step2 f => ackermann_fuel n 1 f
| n + 1, m + 1, .step3 f1 f2 =>
  ackermann_fuel n (ackermann_fuel (n + 1) m f2) (f1 _ (by as_aux_lemma => exact P.intro))
termination_by?
end Test2

namespace Test3
/--
info: Try this:
  termination_by structural x _ x => x
-/
#guard_msgs in
@[expose] public def ackermann_fuel : (n m : Nat) → (fuel : AckFuel n m) → Nat
| 0, m, .step1 => m+1
| n + 1, 0, .step2 f => ackermann_fuel n 1 f
| n + 1, m + 1, .step3 f1 f2 =>
  ackermann_fuel n (ackermann_fuel (n + 1) m f2) (f1 _ (by exact P.intro))
termination_by?
end Test3

namespace Test4

-- This checks that when unfolding abstracted proofs, we do not unfold function calls
-- that were actually there, like the one to `Function.cons` below

/--
error: failed to infer structural recursion:
Cannot use parameter #3:
  unexpected occurrence of recursive application
    ackermann_fuel
-/
#guard_msgs in
public def ackermann_fuel : (n m : Nat) → (fuel : AckFuel n m) → Nat
| 0, m, .step1 => m+1
| n + 1, 0, .step2 f => ackermann_fuel n 1 f
| n + 1, m + 1, .step3 f1 f2 =>
  Function.const _
    ( ackermann_fuel n (ackermann_fuel (n + 1) m f2) (f1 _ (by exact P.intro))
    )
    ackermann_fuel
termination_by structural _ _ fuel => fuel

end Test4
