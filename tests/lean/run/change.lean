
private axiom test_sorry : ∀ {α}, α

set_option linter.missingDocs false
set_option pp.mvars false

example : n + 2 = m := by
  change n + 1 + 1 = _
  guard_target =ₛ n + 1 + 1 = m
  exact test_sorry

example (h : n + 2 = m) : False := by
  change _ + 1 = _ at h
  guard_hyp h :ₛ n + 1 + 1 = m
  exact test_sorry

example : n + 2 = m := by
  fail_if_success change true
  fail_if_success change _ + 3 = _
  fail_if_success change _ * _ = _
  change (_ : Nat) + _ = _
  exact test_sorry

-- `change ... at ...` allows placeholders to mean different things at different hypotheses
example (h : n + 3 = m) (h' : n + 2 = m) : False := by
  change _ + 1 = _ at h h'
  guard_hyp h :ₛ n + 2 + 1 = m
  guard_hyp h' :ₛ n + 1 + 1 = m
  exact test_sorry

-- `change ... at ...` preserves dependencies
example (p : n + 2 = m → Type) (h : n + 2 = m) (x : p h) : false := by
  change _ + 1 = _ at h
  guard_hyp x :ₛ p h
  exact test_sorry

noncomputable example : Nat := by
  fail_if_success change Type 1
  exact test_sorry

def foo (a b c : Nat) := if a < b then c else 0

/-!
The first `change` would fail with `typeclass instance problem is stuck` if we did not have
the `Term.synthesizeSyntheticMVars (postpone := .partial); discard <| isDefEq p e` hint
-/
example : foo 1 2 3 = 3 := by
  change (if _ then _ else _) = _
  change ite _ _ _ = _
  change (if _ < _ then _ else _) = _
  change _ = (if true then 3 else 4)
  rfl

example (h : foo 1 2 3 = 4) : True := by
  change ite _ _ _ = _ at h
  guard_hyp h :ₛ ite (1 < 2) 3 0 = 4
  trivial

example (h : foo 1 2 3 = 4) : True := by
  change (if _ then _ else _) = _ at h
  guard_hyp h : (if 1 < 2 then 3 else 0) = 4
  trivial

example (α : Type) [LT α] (x : α) (h : x < x) : x < id x := by
  change _ < _ -- can defer LT typeclass lookup, just like `show`
  change _ < _ at h -- can defer LT typeclass lookup at h too
  guard_target =ₛ x < id x
  change _ < x
  guard_target =ₛ x < x
  exact h

/-!
basic failure
-/
/--
error: 'change' tactic failed, pattern
  m = ?_
is not definitionally equal to target
  n = m
-/
#guard_msgs in example : n = m := by
  change m = _

/-!
`change` can create new metavariables and assign them
-/
/--
trace: x y z : Nat
w : Nat := x + y
⊢ x + y = z
-/
#guard_msgs in
example (x y z : Nat) : x + y = z := by
  change ?a = _
  let w := ?a
  trace_state
  exact test_sorry

/-!
`change` is allowed to create new goals.
Motivation: sometimes there are proof arguments that need to be filled in, and it is easier to do so as a new goal.
-/
example (x y : Nat) (h : x = y) : True := by
  change (if 1 < 2 then x else ?z) = y at h
  · trivial
  · exact 22

example : let x := 22; let y : Nat := x; let z : Fin (y + 1) := 0; z.1 < y + 1 := by
  intro x y z -- `z` was previously erroneously marked as unused
  change _ at y
  exact z.2

/-!
`change` reorders hypotheses if necessary
-/
/--
trace: x y z w : Nat
a : Nat := x + y
h : a = z + w
⊢ True
-/
#guard_msgs in
example (x y z w : Nat) (h : x + y = z + w) : True := by
  let a := x + y
  change a = _ at h
  trace_state
  trivial

/-!
`change` inserts a coercion when types are incompatible.
-/
example (ty : {α : Prop // Nonempty α}) : ty.val := by
  change ty
  guard_target =ₛ ty.val
  exact test_sorry

/-!
Fails, type hint can't hint enough since `.some _` is postponed.
-/
/--
error: Invalid dotted identifier notation: The expected type of `.some` could not be determined
-/
#guard_msgs in example : some true = (some true).map id := by
  change _ = .some _

/-!
That works with a mild type hint.
-/
example : some true = (some true).map id := by
  change _ = (.some _ : Option _)
  rfl


/-!
## Conv `change`
-/

/-!
conv `change` test
-/
example (m n : Nat) : m + 2 = n := by
  conv => enter [1]; change m + (1 + 1)
  guard_target =ₛ m + (1 + 1) = n
  exact test_sorry

/-!
conv `change` test failure
-/
/--
error: 'change' tactic failed, pattern
  m + n
is not definitionally equal to target
  m + 2
-/
#guard_msgs in
example (m n : Nat) : m + 2 = n := by
  conv => enter [1]; change m + n

/-!
conv `change` unsolved metavariables
-/
/--
error: don't know how to synthesize placeholder for argument `e`
context:
case a
m n : Nat
⊢ Nat
---
error: unsolved goals
m n : Nat
⊢ m + 2 = n
-/
#guard_msgs in
example (m n : Nat) : m + 2 = n := by
  conv => enter [1]; change if True then m + 2 else ?a

/-!
conv `change` to create a metavariable
-/
/--
trace: a b c d : Nat
e : Nat := a + b
⊢ a + b + c = d
-/
#guard_msgs in
example (a b c d : Nat) : a + b + c = d := by
  conv => enter [1,1]; change ?mvar
  let e := ?mvar
  trace_state
  exact test_sorry
