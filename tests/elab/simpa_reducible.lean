/-!
# `simpa using h` final unification at reducible transparency

`simpa using h` checks that the simplified `h` matches the simplified goal at
**reducible** transparency. Semireducible definitions do not unfold during
this check.

`simpa using! h` performs the match at the ambient (default/semireducible)
transparency, recovering the previous behaviour.
-/

def foo : Nat := 37

/-!
With the default, `foo` is not unfolded during the close, so this fails.
-/
/--
error: Type mismatch: After simplification, term
  h
 has type
  @Eq Nat foo n
but is expected to have type
  @Eq Nat 37 n
-/
#guard_msgs in
example (n : Nat) (h : foo = n) : 37 = n := by
  simpa using h

/-!
With `simpa using!`, the previous semireducible behaviour is used and
`foo` reduces to `37` during the close.
-/
example (n : Nat) (h : foo = n) : 37 = n := by
  simpa using! h

/-!
Reducible definitions still unfold during the close under the default.
-/
@[reducible] def fooR : Nat := 37

example (n : Nat) (h : fooR = n) : 37 = n := by
  simpa using h

/-!
`simpa` without `using` is unaffected — the transparency choice only gates
the final unification of the `using`-clause term against the simplified goal.
-/
example (n : Nat) (h : n = n) : n = n := by
  simpa

/-!
Simplification itself is unaffected: `simp` may freely rewrite the goal and
the `using` term; the reducible check applies only to the post-simplification
match.
-/
example (n m : Nat) (h : n + 0 = m) : n = m := by
  simpa using h
