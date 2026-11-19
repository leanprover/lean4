import Lean

/-! These tests ensure that `refine e` only returns goals that were created during elaboration of
`e` (and not before).

Including mvars encountered in `e` that were created at any point in time caused trouble in a
couple of ways:

* Pre-existing goals were duplicated in the infoview (issue #2495)
* "Goal tunneling": natural holes (`_`) created far earlier in the term could suddenly resurface
  after using `refine` on a term that happened to involve them (not documented on the lean4 repo;
  discovered during testing in Mathlib). A schematic example of this sort of issue:
```
def x := {
  /- `field1` introduces a natural mvar: -/
  field1 := f _
  /- the value of `field1` is used in `field2`, and prior to this fix, the goal created above
  "tunnels" into the infoview via `refine'`: -/
  field2 := by refine' <term involving field1> -- includes pre-existing natural mvar
}
```

These issues were fixed in lean4#2502.
-/

/-! # Issue 2495 -/

/- In the following tests we take advantage of the fact that the unsolved goals error reports the
tactic state to ensure that goals haven't been duplicated. -/

/-! Refining using an existing goal (in this case, simply unifying it with the main goal) should
only produce one `case a` in the infoview, not two. -/

example : True := by
  have : True := ?a
  refine ?a -- should produce only one `case a`

/-! Only new goals in the refined expression should replace the main goal. Pre-existing side goals
should stay at the bottom of the list. -/

inductive Foo where
| mk (α : Type) : α → Foo

example : Foo := by
  have h : Type := ?a
  refine .mk ?a ?b
  /- `?a` is a pre-existing goal, `?b` is not; `refine` should only return `?b`, and `?a` should
  remain at the bottom of the goal list. -/

/-! # Goal tunneling -/

/-! Natural mvars created earlier should not be able to tunnel into later uses of `refine`, but
should be solved separately. -/

axiom neq3 {n} : n ≠ 3

structure Bar where
  x : Nat
  y : x ≠ 3

/- This should not work: -/
def bar : Bar := {
  x := _ + 1
  y := by
    refine' neq3 -- captures the underscore above
    exact 0 -- solves it
}

/-!
# Issue #2434

Resolving this issue also resolves issue #2434, which identified an inconsistency in *which*
pre-existing mvars were being preserved --- namely, `refine` would include old pre-existing
syntheticOpaque mvars, but not old natural mvars. This would erroneously close goals. Here, we
demonstrate that uniformly filtering out old mvars also resolves that issue.
-/

open Lean Meta Elab Tactic Term in
/-- `add_natural_goal a : A` adds a new natural goal of type `A` named `a` to the end of the tactic
state. -/
elab "add_natural_goal" s:ident " : " t:term : tactic => do
  let g ← mkFreshExprMVar (← elabType t) .natural s.getId
  appendGoals [g.mvarId!]

/-!
In the following, prior to lean4#2502, `refine` would erroneously close each focused goal, leading
to a `(kernel) declaration has metavariables '_example'` error.
This occurred because `withCollectingNewGoalsFrom` was only erroring on new natural goals (as
determined by `index`), while simultaneously only passing through non-natural goals to construct
the resulting goal list. This orphaned old natural metavariables and closed the goal list
erroneously.
As such, since we now eliminate all old mvars from the resulting goal list with the exception of
the main goal (in which case we effectively no-op) all of the following tests should produce an
`unsolved goals` error.
-/

example : Bool × Nat := by
  add_natural_goal d : Bool
  add_natural_goal e : Nat
  · refine (?d,?e)
  · refine ?d
  · refine ?e

example : Bool × Bool := by
  add_natural_goal d : Bool
  add_natural_goal e : Bool
  · refine (?d,?e)
  · case d => refine ?e
  · refine ?e
