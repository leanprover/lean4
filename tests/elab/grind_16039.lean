/-!
Regression test for #16039: anchors in `grind` parameters take precedence over
user-defined `#` prefix notation.
-/

opaque Q : Nat → Prop
axiom Q_ax (n : Nat) : Q n

prefix:arg "#" => Q_ax

/--
info: Try these:
  [apply] grind only [#f02a]
  [apply] grind only
  [apply] grind => instantiate only [#f02a]
-/
#guard_msgs in
example (P : Nat → Prop) (h : ∀ n, P n) : P 0 := by grind?

example (P : Nat → Prop) (h : ∀ n, P n) : P 0 := by grind only [#f02a]

-- `#` followed by a non-hex identifier still parses as a term parameter.
/-- error: Unknown identifier `nope` -/
#guard_msgs in
example : True := by grind only [#nope]

-- `#ab` is an anchor, but parentheses give access to the notation.
example (ab : Nat) : Q ab := by grind only [(#ab)]

/--
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (ab : Nat) : Q ab := by grind only [#ab]
