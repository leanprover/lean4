import data.nat

inductive Diff ( n : nat ) : nat -> Type :=
| Base : Diff n n
| Step : Π (m : nat), Diff n (nat.succ m) -> Diff n m

definition checkDiff : Π (n m : nat), Diff n m -> Prop
| n _ (Diff.Base n) := true
| n m (Diff.Step m s) := checkDiff n _ s

print checkDiff
