/-!
Regression test for the partial `Expr.appArg!`/`Expr.appFn!` stripping loops in
`Lean.Meta.Simp.SimprocEntry.try`, `SimprocEntry.tryD` and
`Lean.Meta.Simp.tryTheoremCore`.

Each loop strips `numExtraArgs` arguments using the partial accessors without
checking that it still has an application. `numExtraArgs` can exceed the
current application spine in two independent ways:

* in the non-indexed rewriting path, it is computed from a *reduced* form of the
  expression while the stripping happens on the *raw* one, which is what the
  example below exercises: the count comes from `g 0 1`, which has two
  arguments, while `foo 1` has one;
* in `simprocCore`, the candidates and their counts are computed once, but an
  earlier candidate returning `.continue (some r)` rewrites the expression, so a
  later candidate can receive a count for a longer, superseded spine.

When the loop ran off the end, `panic!` returned its `Inhabited` fallback and
`_inhabitedExprDummy` leaked into elaboration, producing a spurious
`Unknown constant` error. Because a panic is logged at `info` severity, builds
still exited successfully while emitting them.
-/

opaque g : Nat → Nat → Unit

@[reducible] def foo : Nat → Unit := g 0

theorem all_unit (x : Unit) : x = () := Subsingleton.elim _ _

-- `all_unit` is reported unused because `simp` closes the goal by other means
-- once it no longer panics; it still has to be in the simp set to reach the
-- rewriting path under test.
set_option linter.unusedSimpArgs false in
example : foo 1 = () := by
  simp (config := { index := false }) only [all_unit]
