/-!
# App elaborator infotrees should have full context when there is ambiguity

This file contains a simplified version of the example in the following issue:
https://github.com/leanprover/lean4/issues/8108
-/

--^ collectDiagnostics

set_option warn.sorry false
set_option pp.mvars false

/-!
The term goal used to have an unknown metavariable.
-/
def mk_cons (I S : Type) : Type := sorry

infixr:50 " >> " => mk_cons

def eq (x y : Nat) : Prop := sorry

def chain := eq >> (eq _)
                     --^ $/lean/plainTermGoal

/-!
Incidentally, ambiguous elaboration used to discard all info trees.
Now we can see that the expected type at `??` is `Nat` despite the ambiguity.
-/
notation "??" => 1
notation "??" => ?_

def test : Nat := ??
                --^ $/lean/plainTermGoal
