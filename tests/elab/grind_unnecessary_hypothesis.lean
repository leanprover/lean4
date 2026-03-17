/-
This is an example posted by Wrenna Robson on Zulip.
-/

-- Reference
def idxToCount [BEq α] (xs : List α) (i : Nat) (hi : i < xs.length) : Nat := go xs i hi 0 where
  @[specialize] go : (xs : List α) → (i : Nat) → i < xs.length → Nat → Nat
  | _ :: _, 0, _, acc => acc
  | x :: xs, i + 1, hi, acc =>
    haveI hi := Nat.lt_of_succ_lt_succ hi
    bif x == xs[i] then go xs i hi (acc + 1) else go xs i hi acc

-- `go` does not depend on the outer `xs` as expected.
/--
info: idxToCount.go.{u_1} {α : Type u_1} [BEq α] (xs : List α) (i : Nat) : i < xs.length → Nat → Nat
-/
#guard_msgs in
#check idxToCount.go


def idxToCount' [BEq α] (xs : List α) (i : Nat) (hi : i < xs.length) : Nat := go xs i hi 0 where
  @[specialize] go : (xs : List α) → (i : Nat) → i < xs.length → Nat → Nat
  | _ :: _, 0, _, acc => acc
  | x :: xs, i + 1, hi, acc =>
    bif x == xs[i]'(by grind) then go xs i (by grind) (acc + 1) else go xs i (by grind) acc

/-
`grind +revert` was the default behavior until v4.25.1
Thus, `go` used to depend on the outer `xs`. This is not the case anymore.
-/
/--
info: idxToCount'.go.{u_1} {α : Type u_1} [BEq α] (xs : List α) (i : Nat) : i < xs.length → Nat → Nat
-/
#guard_msgs in
#check idxToCount'.go

/-
We can reproduce the behavior of v4.25.1 using `grind +revert`.
-/
def idxToCount'' [BEq α] (xs : List α) (i : Nat) (hi : i < xs.length) : Nat := go xs i hi 0 where
  @[specialize] go : (xs : List α) → (i : Nat) → i < xs.length → Nat → Nat
  | _ :: _, 0, _, acc => acc
  | x :: xs, i + 1, hi, acc =>
    bif x == xs[i]'(by grind +revert) then go xs i (by grind +revert) (acc + 1) else go xs i (by grind +revert) acc

/--
info: idxToCount''.go.{u_1} {α : Type u_1} [BEq α] (xs : List α) (i : Nat) (hi : i < xs.length) (xs✝ : List α) (i✝ : Nat) :
  i✝ < xs✝.length → Nat → Nat
-/
#guard_msgs in
#check idxToCount''.go

set_option linter.unusedVariables true
-- Another example from the Zulip thread
/--
warning: unused variable `hi`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
def oops (oh_no : List Nat) (hi : 0 < oh_no.length) : True := go where
  go : True := by grind

/-- info: oops.go : True -/
#guard_msgs in
#check oops.go
