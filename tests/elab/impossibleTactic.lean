import Lean
/-! # Tests for the `impossible` tactic combinator -/

-- Closed goal: the negation has no binders, so the user proves it directly.
/--
warning: declaration uses `sorry`
-/
#guard_msgs in
example : 0 = 1 := by
  impossible by decide

-- When the user's tactic fails to close the negation, the normal `unsolved goals`
-- error is reported (no error suppression).
/--
error: unsolved goals
⊢ ¬0 = 0
-/
#guard_msgs in
example : 0 = 0 := by
  impossible by skip

-- The tactic reverts all hypotheses, so the user can refute the original
-- universal by exhibiting a counter-witness for the local context.
/--
trace: ⊢ ¬∀ (n : Nat), n = n + 1
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (n : Nat) : n = n + 1 := by
  impossible by
    trace_state
    intro h
    exact Nat.succ_ne_zero _ ((h 0).symm)

-- Expression metavariables in the goal are abstracted as additional binders;
-- those are introduced into the local context *before* the user's tactic runs,
-- with the negation pushed under the mvar binders but over the reverted ones.
-- This is what makes `impossible` usable inside an `∃`-introduction.
/--
trace: w : Nat
⊢ ¬w * w = 2
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : ∃ x, x * x = 2 := by
  refine Exists.intro ?w ?h
  case h =>
    impossible by
      trace_state
      intro hx
      cases w <;> grind
  case w =>
    exact 0

-- An mvar whose *type* depends on a reverted local hypothesis gets generalized
-- to a function type (since `revert` produces the right Pi and the original
-- mvar gets replaced with a fresh anonymous one — hence the fallback name
-- `x`, rather than `v`).
/--
warning: declaration uses `sorry`
---
trace: x : (n : Nat) → Vector Nat n
⊢ ¬∀ (n : Nat), (x n)[0]? = some 0
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (n : Nat) : ∃ v : Vector Nat n, v[0]? = some 0 := by
  refine Exists.intro ?v ?h
  case h =>
    impossible by
      trace_state
      sorry
  case v =>
    exact Vector.replicate n 0

-- Goal `False`: `¬False` is `False → False`, which is closed by `exact id`.
/--
warning: declaration uses `sorry`
-/
#guard_msgs in
example : False := by
  impossible by exact id

-- The tactic works at any universe, including non-`Prop` goals: it falls back
-- to `_ → False` instead of `Not _` so the construction is well-typed.
/--
error: unsolved goals
⊢ ∀ (x : Nat), False
-/
#guard_msgs in
example : Nat := by
  impossible by skip

-- Universe parameters of the surrounding declaration are not abstracted: the
-- negated target inherits them as fixed `Type u` / `Type v` binders rather
-- than universe mvars.
/--
error: unsolved goals
⊢ ¬∀ (α : Type u) (β : Type v), ULift α = ULift β
-/
#guard_msgs in
example (α : Type u) (β : Type v) : ULift.{v} α = ULift.{u} β := by
  impossible by skip

-- The proof of the negation is registered as a private aux lemma, which means
-- the kernel re-checks it. A tactic that produces a syntactically well-formed
-- but ill-typed mvar assignment (here, a `Nat` literal where a proof is
-- expected) is therefore rejected by the kernel rather than silently absorbed.
open Lean Lean.Elab Lean.Elab.Tactic in
elab "_fake_close" : tactic => do
  let mvar ← getMainGoal
  mvar.assign (mkNatLit 0)
/--
error: (kernel) declaration type mismatch, '_example._impossible_1' has type
  ¬True → Nat
but it is expected to have type
  ¬¬True
-/
#guard_msgs in
example : ¬True := by
  impossible by
    intro _
    _fake_close

-- An expression metavariable that lives at a lower `mctx` depth (e.g. from a
-- surrounding `withNewMCtxDepth`) still gets abstracted: we want every mvar
-- in the goal to become a universal binder, regardless of its depth, since
-- the resulting type is only used as a proof obligation. The unrelated
-- `(kernel) declaration has metavariables` here comes from the synthetic
-- injection leaving its own outer mvar unassigned and is not part of what
-- `impossible` is being asserted about.
section
open Lean Lean.Elab Lean.Elab.Tactic Lean.Meta in
elab "_with_lower_depth_mvar_goal" : tactic => do
  let lowMVar ← mkFreshExprMVar (mkConst ``Nat)
  let mctx ← Lean.getMCtx
  Lean.setMCtx { mctx with depth := mctx.depth + 1 }
  let goalType := mkApp3 (mkConst ``Eq [.succ .zero]) (mkConst ``Nat) lowMVar (mkNatLit 0)
  let g ← mkFreshExprSyntheticOpaqueMVar goalType
  setGoals [g.mvarId!]
/--
warning: declaration uses `sorry`
---
trace: x : Nat
⊢ ¬x = 0
---
error: (kernel) declaration has metavariables '_example'
-/
#guard_msgs in
example : True := by
  _with_lower_depth_mvar_goal
  impossible by
    trace_state
    intro h
    exact (by sorry : False)
end

-- The tactic should complain if the goal contains universe metavariables. We
-- have to inject one manually since user-level `Sort _` is auto-bound.
section
open Lean Lean.Elab.Tactic in
elab "with_level_mvar_goal" : tactic => do
  let lvl ← Lean.Meta.mkFreshLevelMVar
  let ty := mkApp (mkConst ``Subsingleton [lvl]) (mkSort lvl)
  let g ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar ty
  setGoals [g.mvarId!]
set_option pp.mvars false in
/--
error: `impossible`: goal contains universe metavariables
  Subsingleton (Sort _)
-/
#guard_msgs in
example : True := by
  with_level_mvar_goal
  impossible by skip
end

-- The `+levels` option abstracts universe parameters of the surrounding
-- declaration as fresh level metavariables in the negated goal, so the user
-- can refute a universe-polymorphic claim by exhibiting witnesses at
-- specific universes. Note that the level pretty-printer doesn't preserve
-- the original universe parameter names — they show as `?u.<N>`/`?u.<M>`
-- in the goal state.
set_option pp.mvars false in
/--
trace: ⊢ ¬∀ (α : Type _) (β : Type _), ¬ULift α = ULift β
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (α : Type u) (β : Type v) : ¬(ULift.{v} α = ULift.{u} β) := by
  impossible +levels by
    trace_state
    intro h
    -- Specializing at `Unit : Type 0` unifies both universe mvars.
    exact h Unit Unit rfl

-- If the inner tactic doesn't pin down all the level mvars (e.g. it uses
-- `sorry` without constraining them), `mkAuxTheorem` closes over the
-- remaining level mvars as fresh universe parameters of the auxiliary
-- lemma. Semantically: a counter-example that works at any level is a
-- *parametric* counter-example, which is fine — we don't need to spuriously
-- pin a universe just to make the kernel happy.
/--
warning: declaration uses `sorry`
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (α : Type u) (β : Type v) : ¬(ULift.{v} α = ULift.{u} β) := by
  impossible +levels by
    intro _
    exact sorry

-- Errors in the user's term/tactic are surfaced normally.
/--
error: Unknown identifier `this_identifier_does_not_exist`
-/
#guard_msgs in
example (n : Nat) : n = 0 := by
  impossible by intro h; exact this_identifier_does_not_exist

-- `impossible` plays well with surrounding tactic combinators.
/--
warning: declaration uses `sorry`
-/
#guard_msgs in
example : 0 = 1 := by
  first | impossible by decide | exact rfl

-- `impossible` fails when there is no goal.
/--
error: No goals to be solved
-/
#guard_msgs in
example : True := by
  trivial
  impossible by skip

-- With multiple goals, `impossible` only admits the first; the second is left
-- for the next tactic.
/--
warning: declaration uses `sorry`
-/
#guard_msgs in
example : 0 = 1 ∧ True := by
  constructor
  impossible by decide
  trivial
