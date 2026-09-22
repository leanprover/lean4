/-!
Regression test for issue #14441: a hypothesis such as `h : a = b → False` has the shape of a
`match`-expression condition, so `grind` processes it using the `Grind.MatchCond` machinery.
`tryToProveFalse` then invoked `isDefEqD a b` with default transparency, triggering an
arbitrarily expensive `whnf` reduction (here: unfolding a 256-element `Array.ofFn`).
Now the congruence closure is consulted first, and the `isDefEq` fallback only runs when the
equation's right-hand side is pattern-like (metavariable, constructor application, or literal).
-/

def init (x : Nat) : Array Nat := Array.ofFn (n := 256) (fun _ => x)

-- The goal follows from `hneg h`; no `whnf` reduction of `init` should happen.
set_option maxHeartbeats 1000 in
example (c0 c1 : Nat)
    (h    : init c0 = init c1)
    (hneg : init c0 = init c1 → False) :
    False := by
  grind

-- The mere presence of `hneg` must not trigger the reduction either.
set_option linter.unusedVariables false in
set_option maxHeartbeats 1000 in
example (c0 c1 : Nat) (a : Nat)
    (hneg : init c0 = init c1 → False)
    (h2 : a = 1) :
    a = 1 := by
  grind
