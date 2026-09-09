/-!
Tests that a non-monadic, non-tail-recursive `partial_fixpoint` definition (nested recursive call
`f91 (f91 …)`) reports a helpful monotonicity error rather than a confusing `Unknown constant`
error. Previously the fixed-parameter analysis and the functor construction failed to descend into
the arguments of a recursive call, leaving the not-yet-defined constant behind.
-/

/--
error: Could not prove 'f91' to be monotone in its recursive calls:
  Cannot eliminate recursive call `f91 (n + 11)` enclosed in
    f91 (f91 (n + 11))
-/
#guard_msgs in
def f91 (n : Nat) : Nat :=
  if n > 100
    then n - 10
    else f91 (f91 (n + 11))
partial_fixpoint
