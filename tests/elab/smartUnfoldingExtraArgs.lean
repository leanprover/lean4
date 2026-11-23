module

/-!
Smart unfolding must check marked matches in the selected branch of a function-valued
match and in arguments supplied to the resulting function.
-/

private def higherFlag (n : Nat) (flag : Bool) (u : Nat) : Nat :=
  match n with
  | 0 => u
  | n+1 =>
    (match flag with
     | false => fun a => a
     | true => match n with
       | 0 => fun a => a+1
       | k+1 => fun a => higherFlag k true a) u
termination_by structural n

example (n u : Nat) : higherFlag (n+1) true u =
    (match n with | 0 => fun a => a+1 | k+1 => fun a => higherFlag k true a) u := by
  fail_if_success exact rfl
  cases n <;> rfl

example (P : Nat → Prop) (n u : Nat) (h : P u) : P (higherFlag (n+1) false u) := by
  dsimp (config := { autoUnfold := true }) only
  guard_target =ₛ P u
  exact h

example (P : Nat → Prop) (k u : Nat) (h : P (higherFlag k true u)) : P (higherFlag (k+2) true u) := by
  dsimp (config := { autoUnfold := true }) only
  guard_target =ₛ P (higherFlag k true u)
  exact h

-- The first extra argument can be consumed before the selected branch reaches a marked match.
private def curriedFlag (n : Nat) (flag : Bool) (x y : Nat) : Nat :=
  match n with
  | 0 => x+y
  | n+1 =>
    (match flag with
     | false => fun a b => a+b
     | true => fun a => match n with
       | 0 => fun b => a+b
       | k+1 => fun b => curriedFlag k true a b) x y
termination_by structural n

example (P : Nat → Prop) (n x y : Nat) (h : P (curriedFlag (n+1) true x y)) :
    P (curriedFlag (n+1) true x y) := by
  fail_if_success dsimp (config := { autoUnfold := true }) only
  exact h

private def fromArg (n : Nat) (flag : Bool) : Nat :=
  match n with
  | 0 => 0
  | n+1 =>
    (match flag with | true => fun a => a | false => fun a => a+1)
      (match n with | 0 => 5 | k+1 => fromArg k flag)
termination_by structural n

example (n : Nat) : fromArg (n+1) true = (match n with | 0 => 5 | k+1 => fromArg k true) := by
  fail_if_success exact rfl
  cases n <;> rfl

example (P : Nat → Prop) (k : Nat) (h : P (fromArg k true)) : P (fromArg (k+2) true) := by
  dsimp (config := { autoUnfold := true }) only
  guard_target =ₛ P (fromArg k true)
  exact h
