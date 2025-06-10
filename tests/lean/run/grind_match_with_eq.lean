set_option grind.warning false

def f (a : Option Nat) (h : a ≠ none) : Nat :=
 match a with
 | some a => a
 | none => by grind

def g (a : Option Nat) : Nat :=
  match h : a with
  | none => 1
  | some _ => f a (by grind) + 1

example : g a > 0 := by
  unfold g
  grind
