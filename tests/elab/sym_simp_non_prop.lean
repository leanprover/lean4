import Lean
/-!
Tests that `Sym.simp` produces a proper error message (instead of the internal
error `unexpected bound variable #3`) when a declaration or local hypothesis
that is not a proposition is used as a simp theorem.
-/

/--
error: cannot use `HAdd.hAdd` as a simp theorem, its type is not a proposition
  {α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HAdd α β γ] → α → β → γ
-/
#guard_msgs in
example : 1 + 1 = 2 := by
  sym =>
    simp [HAdd.hAdd]

/--
error: cannot use as a simp theorem, its type is not a proposition
  Nat
-/
#guard_msgs in
example (x : Nat) : x + 0 = x := by
  sym =>
    simp [x]

def myDef : Prop := True

/--
error: cannot use `myDef` as a simp theorem, its type is not a proposition
  Prop
-/
#guard_msgs in
example : 1 + 1 = 2 := by
  sym =>
    simp [myDef]
