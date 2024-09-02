opaque q : Nat → Nat
def f (x : Nat) : Nat :=
  match x with
  | 0 => 1
  | x+1 => q (f x)

theorem f_eq : f (x + 1) = q (f x) := rfl

set_option trace.Meta.debug true

/--
info: [reduction] unfolded declarations (max: 15, num: 6):
  [reduction] Nat.rec ↦ 15
  [reduction] Add.add ↦ 10
  [reduction] HAdd.hAdd ↦ 10
  [reduction] Nat.add ↦ 10
  [reduction] f ↦ 5
  [reduction] OfNat.ofNat ↦ 5[reduction] unfolded instances (max: 5, num: 1):
  [reduction] instOfNatNat ↦ 5[reduction] unfolded reducible declarations (max: 15, num: 1):
  [reduction] Nat.casesOn ↦ 15use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
example : f (x + 5) = q (q (q (q (q (f x))))) :=
  set_option diagnostics.threshold 4 in
  set_option diagnostics true in
  rfl

/--
info: [reduction] unfolded declarations (max: 15, num: 6):
  [reduction] Nat.rec ↦ 15
  [reduction] Add.add ↦ 10
  [reduction] HAdd.hAdd ↦ 10
  [reduction] Nat.add ↦ 10
  [reduction] f ↦ 5
  [reduction] OfNat.ofNat ↦ 5[reduction] unfolded instances (max: 5, num: 1):
  [reduction] instOfNatNat ↦ 5[reduction] unfolded reducible declarations (max: 15, num: 1):
  [reduction] Nat.casesOn ↦ 15use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
-/
#guard_msgs in
example : f (x + 5) = q (q (q (q (q (f x))))) := by
  set_option diagnostics.threshold 4 in
  set_option diagnostics true in
  rfl
