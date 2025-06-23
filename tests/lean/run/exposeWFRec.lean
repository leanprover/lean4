module

set_option pp.proofs true

-- Non-exposed all is fine
def ack : Nat → Nat → Nat
| 0, m => m+1
| n + 1, 0 => ack n 1
| n + 1, m + 1 => ack n (ack (n + 1) m)
termination_by n m => (n,m)

/--
error: (kernel) unknown constant '_private.«external:file:///home/joachim/lean4/tests/lean/run/exposeWFRec.lean».0.ackermann._proof_3'
---
error: (kernel) unknown constant '_private.«external:file:///home/joachim/lean4/tests/lean/run/exposeWFRec.lean».0.ackermann._proof_3'
---
error: (kernel) unknown constant '_private.«external:file:///home/joachim/lean4/tests/lean/run/exposeWFRec.lean».0.ackermann._proof_3'
-/
#guard_msgs in
@[expose] def ackermann : Nat → Nat → Nat
| 0, m => m+1
| n + 1, 0 => ackermann n 1
| n + 1, m + 1 => ackermann n (ackermann (n + 1) m)
termination_by n m => (n,m)

def ack_steps : Nat → Nat → Nat
| 0, _ => 0
| n + 1, 0 => 1 + ack_steps n 1
| n + 1, m + 1 =>1 + max (ack_steps n (ack (n + 1) m)) (ack_steps (n + 1) m)
termination_by n m => (n,m)

axiom P : Nat → Prop
axiom P.intro : P n

inductive AckFuel : (n m : Nat) → Type where
  | step1 : AckFuel 0 m
  | step2 : AckFuel n 1 → AckFuel (n + 1) 0
  | step3 : (∀ m', P m' → AckFuel n m') → AckFuel (n + 1) m → AckFuel (n+1) (m + 1)

def ackermann_fuel : (n m : Nat) → (fuel : AckFuel n m) → Nat
| 0, m, .step1 => m+1
| n + 1, 0, .step2 f => ackermann_fuel n 1 f
| n + 1, m + 1, .step3 f1 f2 =>
  ackermann_fuel n (ackermann_fuel (n + 1) m f2) (f1 _ (by exact P.intro))
termination_by structural _ _ fuel => fuel

/--
error: (kernel) unknown constant '_private.«external:file:///home/joachim/lean4/tests/lean/run/exposeWFRec.lean».0.foo._proof_3'
-/
#guard_msgs in
@[expose] def foo : Nat → Nat → Nat
| 0, m => m
| n + 1, m => foo n (m+1)
termination_by n m => (n, m)

@[expose] def foo' : Nat → Nat → Nat
| 0, m => m
| n + 1, m => foo' n (m+1)
termination_by n => n
