import Lean
/-!
# Additional tests that syntaxes pretty print with spaces
-/

namespace Damiano1
/-!
These are some pretty printing issues reported by Damiano Testa at
https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Some.20pretty.20printing.20quirks/near/529964215
-/

elab "#pp " cmd:command : command => Lean.logInfo cmd

/-- info: example (h : False) : False := by rcases (h) -/
#guard_msgs in
#pp
example (h : False) : False := by
  rcases (h)

structure X where
  A : {_ : Nat} → Nat → Nat

/-- info: example : X where A {a} b := a + b -/
#guard_msgs in
#pp
example : X where
  A {a} b := a + b

/--
info: example : True :=
  have (h) := trivial
  h
-/
#guard_msgs in
#pp
example : True :=
  have (h) := trivial
  h

/--
info: example (h : ∀ a : Nat, a = a) : 0 = 0 := by
  replace (h) := h 0
  exact h
-/
#guard_msgs in
#pp
example (h : ∀ a : Nat, a = a) : 0 = 0 := by
  replace (h) := h 0
  exact h

/--
info: example {c : Bool} : c = c := by
  induction c with
  | true
  | _ => rfl
-/
#guard_msgs in
#pp
example {c : Bool} : c = c := by
  induction c with
  | true | _ => rfl

/-- info: #check ``Nat -/
#guard_msgs in
#pp
#check ``Nat

/--
info: example : True := by {
  trivial
  done
  done
}
-/
#guard_msgs in
#pp
example : True := by {
  trivial
  done
  done
}

/-- info: example : True := by { trivial } -/
#guard_msgs in
#pp
example : True := by {
  trivial
}

end Damiano1
