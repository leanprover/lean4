/-! A `def` contract, a `for … invariant` clause or an `assert` element used without the `Std`
metatheory reports a helpful error naming the missing import, rather than a downstream elaboration
failure. -/

/--
error: `requires`/`ensures` contracts elaborate to a `vcgen`-proved specification theorem; add `import Std.Internal.Do` to use them.
-/
#guard_msgs in
def f (x : Nat) : Id Nat requires x > 0 ensures r => r ≥ x := pure x

/-- error: the `invariant` clause elaborates to a `vcgen` gadget; add `import Std.Internal.Do` to use it. -/
#guard_msgs in
def g (xs : List Nat) : Id Nat := do
  let mut acc := 0
  for x in xs invariant pref suff => 0 ≤ acc do
    acc := acc + x
  return acc

/-- error: the `assert` element elaborates to a `vcgen` gadget; add `import Std.Internal.Do` to use it. -/
#guard_msgs in
def h (n : Nat) : Id Nat := do
  assert n > 0
  return n
