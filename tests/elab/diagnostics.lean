opaque q : Nat → Nat
def f (x : Nat) : Nat :=
  match x with
  | 0 => 1
  | x+1 => q (f x)

theorem f_eq : f (x + 1) = q (f x) := rfl

/--
trace: [diag] Diagnostics
  [reduction] unfolded declarations (max: 10, num: 1):
    [reduction] Nat.rec ↦ 10
  [reduction] unfolded reducible declarations (max: 10, num: 1):
    [reduction] Nat.casesOn ↦ 10
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
example : f (x + 5) = q (q (q (q (q (f x))))) :=
  set_option diagnostics.threshold 5 in
  set_option diagnostics true in
  rfl

/--
trace: [diag] Diagnostics
  [reduction] unfolded declarations (max: 10, num: 1):
    [reduction] Nat.rec ↦ 10
  [reduction] unfolded reducible declarations (max: 10, num: 1):
    [reduction] Nat.casesOn ↦ 10
  use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
example : f (x + 5) = q (q (q (q (q (f x))))) := by
  set_option diagnostics.threshold 5 in
  set_option diagnostics true in
  rfl
