/-!
# App elaborator infotrees should have full context when there is ambiguity

This file contains a simplified version of the example in the following issue:
https://github.com/leanprover/lean4/issues/8108

The term goal used to have an unknown metavariable.
-/

def mk_cons (I S : Type) : Type := sorry

infixr:50 " >> " => mk_cons

def eq (x y : Nat) : Prop := sorry

def chain := eq >> (eq _)
                     --^ $/lean/plainTermGoal
