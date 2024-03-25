/-!
# Testing `set_equation_theorems`
-/

def myComp (f : β → γ) (g : α → β) : α → γ := fun x => f (g x)

/-- error: failed to rewrite using equation theorems for 'myComp' -/
#guard_msgs in
example (f : γ → δ) (g : β → γ) (h : α → β) :
    myComp f (myComp g h) = myComp (myComp f g) h := by
  rw [myComp]

theorem myComp_eq : myComp f g = fun x => f (g x) := rfl

set_equation_theorems myComp [myComp_eq]

example (f : γ → δ) (g : β → γ) (h : α → β) :
    myComp f (myComp g h) = myComp (myComp f g) h := by
  rw [myComp, myComp, myComp, myComp]
