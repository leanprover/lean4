/-!
Tests that the functional induction principle of a function defined by well-founded recursion
with a nested recursive call has one induction hypothesis per recursive call. The termination proof
of the outer call used to mention the inner call in its type, which led to a second, duplicate
hypothesis for the inner call.
-/

def loopSplit (base : Nat) (n prec : Nat) (acc : List Nat) : List Nat :=
  if prec ≤ 16 then acc else
    let k := prec / 2
    loopSplit base (n / base ^ k) (prec - k) (loopSplit base (n % base ^ k) k acc)
termination_by prec

/--
info: loopSplit.induct : ∀ (base : Nat) (motive : Nat → Nat → List Nat → Prop),
  (∀ (n prec : Nat) (acc : List Nat), prec ≤ 16 → motive n prec acc) →
    (∀ (n prec : Nat) (acc : List Nat),
        ¬prec ≤ 16 →
          have k := prec / 2;
          motive (n % base ^ k) k acc →
            motive (n / base ^ k) (prec - k) (loopSplit base (n % base ^ k) k acc) → motive n prec acc) →
      ∀ (n prec : Nat) (acc : List Nat), motive n prec acc
-/
#guard_msgs in
#check @loopSplit.induct
