/-!
Checks that that the wfrec unfold theorem can be generated even if the
function type is not manifestly a forall.
-/

def T := Nat → Nat

def f : T
| 0 => 0
| n + 1 => f n + 1
termination_by n => n
