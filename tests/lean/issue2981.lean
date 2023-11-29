/-!
Terms are often duplicated in lean. One example is default arguments
referring to earlier ones; observed in the wild with `Array.foldl` and friends.

Ideally, compiling a recursive definition will still only consider such a recursive call once.
-/

def dup (a : Nat) (b : Nat := a) := a + b

namespace TestingFix

def rec : Nat → Nat
 | 0 => 1
 | n+1 => dup (dup (dup (rec n)))
decreasing_by trace "Tactic is run (ideally only once)"; decreasing_tactic

end TestingFix

namespace TestingGuessLex

-- GuessLex should run the tactic an extra time, that is expected
def rec : Nat → Nat → Nat
 | 0, _m => 1
 | n+1, m => dup (dup (dup (rec n (m + 1))))
decreasing_by trace "Tactic is run (ideally only twice)"; decreasing_tactic

end TestingGuessLex
