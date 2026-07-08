/-!
The expected type used to show "unknown metavariable '?_uniq.31828'" because of missing
backtracking of the info tree.
-/

inductive Fam2 : Type → Type → Type 1 where
  | any : Fam2 α α
  | nat : Nat → Fam2 Nat Nat

example (a : α) (x : Fam2 α β) : β :=
  match x with
  | Fam2.any   => _
                --^ $/lean/plainTermGoal
  | Fam2.nat n => n
