module

set_option pp.proofs true

axiom P : Nat → Prop
axiom P.intro : P n

inductive AckFuel : (n m : Nat) → Type where
  | step1 : AckFuel 0 m
  | step2 : AckFuel n 1 → AckFuel (n + 1) 0
  | step3 : (∀ m', P m' → AckFuel n m') → AckFuel (n + 1) m → AckFuel (n+1) (m + 1)

-- set_option trace.Elab.definition true
-- set_option trace.Elab.definition.structural true

def ackermann_fuel : (n m : Nat) → (fuel : AckFuel n m) → Nat
| 0, m, .step1 => m+1
| n + 1, 0, .step2 f => ackermann_fuel n 1 f
| n + 1, m + 1, .step3 f1 f2 =>
  ackermann_fuel n (ackermann_fuel (n + 1) m f2) (f1 _ (by exact P.intro))
termination_by structural _ _ fuel => fuel

/--
error: failed to infer structural recursion:
Cannot use parameter #3:
  unexpected occurrence of recursive application
    ackermann_fuel'
-/
#guard_msgs in
@[expose] def ackermann_fuel' : (n m : Nat) → (fuel : AckFuel n m) → Nat
| 0, m, .step1 => m+1
| n + 1, 0, .step2 f => ackermann_fuel' n 1 f
| n + 1, m + 1, .step3 f1 f2 =>
  ackermann_fuel' n (ackermann_fuel' (n + 1) m f2) (f1 _ (by exact P.intro))
termination_by structural _ _ fuel => fuel
