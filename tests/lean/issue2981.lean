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


namespace Subcontext

set_option linter.unusedVariables false

-- Now with a duplication into another context
-- We thread through `x` so that we can make the context mention something
-- that appears in the goal, else `mvarId.cleanup` will remove it
def dup2 (x : Nat) (a : Nat) (b : x ≠ x → Nat := fun h => a) := a

namespace TestingFix
def rec : Nat → Nat
 | 0 => 1
 | n+1 => dup2 n (rec n)
decreasing_by
  trace "Tactic is run (ideally only once, in most general context)"
  trace_state
  decreasing_tactic

end TestingFix

namespace TestingGuessLex

-- GuessLex should run the tactic an extra time, that is expected
def rec : Nat → Nat → Nat
 | 0, _m => 1
 | n+1, m => dup2 n (rec n (m + 1))
decreasing_by
  trace "Tactic is run (ideally only twice, in most general context)"
  trace_state
  decreasing_tactic

end TestingGuessLex
