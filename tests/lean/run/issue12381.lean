/-!
# Issue 12381: Typeclass inference fails if argument is a `match`

Typeclass inference should succeed even when the argument contains a `match`
expression with a metavariable discriminant.
-/

class Test (n : Nat)

instance {n} : Test n := ⟨⟩

-- These all work
#synth Test 1
#synth Test (if ?_ == 0 then 1 else 1)
#synth Test ?_

-- Match with metavar discriminant (was failing: isDefEqStuck propagated out)
#synth Test (match ?_ with | 0 => 1 | _ => 1)

-- Nested stuck match inside another argument
class Test2 (n m : Nat)
instance {n m} : Test2 n m := ⟨⟩
#synth Test2 1 (match ?_ with | 0 => 1 | _ => 1)
