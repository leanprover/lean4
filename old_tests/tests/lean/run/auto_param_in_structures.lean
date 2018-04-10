namespace test
open tactic
meta def my_tac : tactic unit := abstract (intros >> `[simp])

local attribute [simp] add_assoc mul_assoc

structure monoid (α : Type) :=
(op    : α → α → α)
(assoc : ∀ a b c, op (op a b) c = op a (op b c) . my_tac)

def m1 : monoid nat :=
monoid.mk (+)

def m2 : monoid nat :=
monoid.mk (*)

#print m1
#print m2

def m3 : monoid nat :=
{op := (+)}

def m4 : monoid nat :=
{op := (*)}

#print m3
#print m4

end test
