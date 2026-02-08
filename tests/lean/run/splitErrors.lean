/-! # `split` tactic errors

Assesses error messages and hints produced by the `split` tactic.
-/

/--
error: Tactic `split` failed: Specifying a term to split is not supported yet

Hint: To apply `split` at the hypothesis `h`, use `split at h`:
  split a̲t̲ ̲h
-/
#guard_msgs in
example : False := by
  have h : if True then True else True := trivial
  split h

/-- error: Tactic `split` failed: Specifying a term to split is not supported yet -/
#guard_msgs in
example (x y : Bool) : (if x && y then 1 else 2) > (if x || y then 0 else 1) := by
  split x && y

/--
error: Tactic `split` failed: Could not split an `if` or `match` expression in the goal

Hint: Use `set_option trace.split.failure true` to display additional diagnostic information

⊢ False
-/
#guard_msgs in
example : False := by
  split

/--
error: Tactic `split` failed: Could not split the goal or any of the following hypotheses: `h1`

Note: `split at *` does not attempt to split at non-propositional hypotheses or those on which other hypotheses depend. It may still be possible to manually split a hypothesis using `split at`

Hint: Use `set_option trace.split.failure true` to display additional diagnostic information

h1 : True
⊢ False
-/
#guard_msgs in
example : False := by
  have h1 : True := trivial
  split at *

/--
error: Tactic `split` failed: Could not split an `if` or `match` expression in the type `p ∧ q` of `h`

Hint: If you meant to destruct this conjunction, use the `cases` tactic instead

Hint: Use `set_option trace.split.failure true` to display additional diagnostic information

p q : Prop
h : p ∧ q
⊢ p
-/
#guard_msgs in
example {p q : Prop} (h : p ∧ q) : p := by
  split at h

/--
error: Tactic `split` failed: Could not split an `if` or `match` expression in the type `Equivalence R` of `h`

Hint: If you meant to destruct this structure, use the `cases` tactic instead

Hint: Use `set_option trace.split.failure true` to display additional diagnostic information

α : Sort u_1
R : α → α → Prop
h : Equivalence R
⊢ False
-/
#guard_msgs in
example {R : α → α → Prop} (h : Equivalence R) : False := by
  split at h

/--
error: Tactic `split` failed: Could not split the goal or any of the following hypotheses: `t`, `use_dep`

Note: `split at *` does not attempt to split at non-propositional hypotheses or those on which other hypotheses depend. It may still be possible to manually split a hypothesis using `split at`

t : True
dep : if 1 ≥ 0 then True else False
use_dep : dep = dep
⊢ False
-/
#guard_msgs in
example : False := by
  have t : True := trivial
  have dep : if 1 ≥ 0 then True else False := by simp
  have use_dep : dep = dep := rfl
  set_option trace.split.failure true in
  split at *

/--
error: Tactic `split` failed: Could not split an `if` or `match` expression in the type `Nat` of `x`

x : Nat := if true = true then 3 else 4
⊢ False
-/
#guard_msgs in
example : False := by
  let x := if true then 3 else 4
  set_option trace.split.failure true in
  split at x

/--
error: Tactic `split` failed: Could not split an `if` or `match` expression in the type `True` of `h`

Hint: Use `set_option trace.split.failure true` to display additional diagnostic information

h : True
⊢ False
-/
#guard_msgs in
example : False := by
  have h : True := trivial
  split at h
