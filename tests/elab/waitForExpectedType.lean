/-!
Tests for the `wait_for_expected_type%` term elaborator. It postpones elaborating its argument while the
expected type is an unassigned metavariable, so an `outParam` determined by instance synthesis is
resolved first. Here that keeps the folded carrier `Carrier` folded instead of having the argument
unfold it into `Nat → Nat`.
-/

def Carrier : Type := Nat → Nat
class Sel (α : Type) (β : outParam Type) where
instance : Sel Unit Carrier := ⟨⟩
def sel {α β} [Sel α β] (_ : α) (g : β) : β := g

/-- info: sel () fun n => n : Carrier -/
#guard_msgs in
#check sel () (wait_for_expected_type% (fun n => n))

/-- info: sel () fun n => n : Nat → Nat -/
#guard_msgs in
#check sel () (fun n => n)

/-- info: 5 : Nat -/
#guard_msgs in
#check wait_for_expected_type% (5 : Nat)
