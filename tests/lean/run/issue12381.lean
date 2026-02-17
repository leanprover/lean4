/-!
# Issue 12381: Typeclass inference fails if argument is a `match`

Typeclass inference should succeed even when the argument contains a `match`
expression or other stuck terms, since they are not relevant to instance selection.
-/

class Test (n : Nat)

instance {n} : Test n := ⟨⟩

-- These all work
#synth Test 1
#synth Test (if ?_ == 0 then 1 else 1)

-- Plain metavar works (already handled)
#synth Test ?_

-- Match with metavar discriminant (was failing: isDefEqStuck propagated out)
#synth Test (match ?_ with | 0 => 1 | _ => 1)

-- Reducible def stuck on metavar
@[reducible] def myId (n : Nat) : Nat := n
#synth Test (myId ?_)

-- Nested stuck match inside another argument
class Test2 (n m : Nat)
instance {n m} : Test2 n m := ⟨⟩
#synth Test2 1 (match ?_ with | 0 => 1 | _ => 1)
