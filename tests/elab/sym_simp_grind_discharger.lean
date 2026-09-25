import Lean

/-!
Tests for using `grind` as a `Sym.simp` discharger (`Grind.Goal.mkSymSimpDischarger`).

The test defines a `simp_grind` tactic for `sym =>` mode: `Sym.simp` with the side
conditions of conditional rewrite rules discharged by `grind`. The discharger shares a
`GoalState` whose local context prefix has been internalized once (`Goal.internalizeAll`);
each discharge attempt only internalizes the local declarations introduced after that
(e.g., hypotheses introduced by `Sym.simp` when entering binders).
-/

open Lean Meta Elab Tactic.Grind

syntax (name := symSimpGrind) "simp_grind" (" [" ident,* "]")? : grind

-- Example for using `grind` discharger programmatically
@[grind_tactic symSimpGrind] def evalSymSimpGrind : GrindTactic := fun stx => withMainContext do
  ensureSym
  let `(grind| simp_grind $[[ $[$extraIds],* ]]?) := stx | throwUnsupportedSyntax
  let declNames ← (extraIds.getD #[]).mapM fun id => realizeGlobalConstNoOverload id
  let goal ← getMainGoal
  -- Internalize the remaining hypotheses once; the resulting state is shared by all
  -- discharge attempts, which only internalize declarations introduced during `simp`.
  let goal ← liftGrindM <| Grind.Goal.internalizeAll goal
  if goal.inconsistent then
    -- The goal was closed during internalization.
    replaceMainGoal []
    return
  let d ← liftGrindM <| goal.mkSymSimpDischarger
  let rewrite ← Sym.mkSimprocFor declNames d
  let methods : Sym.Simp.Methods := {
    pre  := Sym.Simp.simpControl.andThen Sym.Simp.simpArrowTelescope
    post := Sym.Simp.evalGround.andThen rewrite
  }
  let result ← liftGrindM <| goal.mvarId.withContext do
    Sym.simp (← goal.mvarId.getType) methods
  match (← liftGrindM <| Sym.Simp.Result.toSimpGoalResult result goal.mvarId) with
  | .closed => replaceMainGoal []
  | .goal mvarId => replaceMainGoal [{ goal with mvarId }]
  | .noProgress => throwError "`simp_grind` made no progress"

opaque f : Nat → Nat
opaque g : Nat → Nat
axiom f_idem (a : Nat) (_h : 0 < a) : f (f a) = f a

-- Side condition `0 < n` follows from `h : 5 ≤ n` by linear arithmetic;
-- a plain assumption discharger would fail here.
example (n : Nat) (h : 5 ≤ n) : f (f n) = f n := by
  sym =>
    simp_grind [f_idem]

-- Ground side condition `0 < 3`.
example : f (f 3) = f 3 := by
  sym =>
    simp_grind [f_idem]

-- Side condition `0 < g n` requires instantiating the quantified hypothesis `h` (E-matching).
example (n : Nat) (h : ∀ x, 0 < g x) : f (f (g n)) = f (g n) := by
  sym =>
    simp_grind [f_idem]

opaque p : {P : Prop} → P → Nat

-- The hypothesis `h : 5 ≤ n` is introduced by `Sym.simp` when entering the dependent
-- binder, i.e., it is *not* part of the internalized local context prefix shared by all
-- discharge attempts. (Note: non-dependent arrows are simplified non-contextually by
-- `simpArrowTelescope`, so their antecedents never reach the discharger.)
/--
error: `sym` failed
case grind
n : Nat
⊢ ∀ (h : 5 ≤ n), f n + p h = 0
[grind] Goal diagnostics
  [facts] Asserted facts
-/
#guard_msgs in
example (n : Nat) : ∀ (h : 5 ≤ n), f (f n) + p h = 0 := by
  sym =>
    simp_grind [f_idem]

-- Discharging `0 < m` needs both the internalized prefix hypothesis `h₁` and the
-- binder-introduced hypothesis `h`.
/--
error: `sym` failed
case grind
n m : Nat
h₁ : 2 ≤ n
⊢ ∀ (h : n ≤ m), f m + p h = 0
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] 2 ≤ n
  [eqc] True propositions
    [prop] 2 ≤ n
-/
#guard_msgs in
example (n m : Nat) (h₁ : 2 ≤ n) : ∀ (h : n ≤ m), f (f m) + p h = 0 := by
  sym =>
    simp_grind [f_idem]

-- Failure: `0 < n` cannot be discharged, so `f_idem` must not be applied.
-- `Nat.add_zero` still fires, so `Sym.simp` makes progress and leaves the goal below.
/--
error: `sym` failed
case grind
n : Nat
⊢ f (f n) = f n
[grind] Goal diagnostics
  [facts] Asserted facts
-/
#guard_msgs in
example (n : Nat) : f (f n) + 0 = f n + 0 := by
  sym =>
    simp_grind [f_idem, Nat.add_zero]

-- The side condition `0 < n` does not hold, but the hypotheses are contradictory.
-- They are introduced without internalization, so the contradiction is only detected
-- when `simp_grind` internalizes them, closing the goal.
example (n : Nat) : n = 0 → n = 1 → f (f n) = f n := by
  sym =>
    intro (internalize := false) h₁ h₂
    simp_grind [f_idem]

-- Here the contradiction is only found by E-matching `h` during a discharge attempt.
example (n : Nat) (h : ∀ x, g x = 0) (h₂ : g 5 = 1) : f (f n) = f n := by
  sym =>
    simp_grind [f_idem]

opaque r : Nat → Nat → Prop
axiom f_r (a w : Nat) (_h : r a w) : f (f a) = f a

-- The value `w` is not covered by the pattern, so the discharger receives the non-Prop
-- side condition `Nat`. `grind` fails gracefully (the hypotheses are consistent), and
-- the rewrite is not applied.
/--
error: `simp_grind` made no progress
-/
#guard_msgs in
example (n : Nat) : f (f n) = f n := by
  sym =>
    simp_grind [f_r]

/-! ## The `with grind` discharger in the simproc DSL -/

register_sym_simp fIdemGrind where
  pre  := control >> arrow_telescope
  post := ground >> rewrite [f_idem] with grind

-- The hypotheses internalized when the `sym =>` block starts are shared by all
-- discharge attempts.
example (n : Nat) (h : 5 ≤ n) : f (f n) = f n := by
  sym =>
    simp fIdemGrind

-- E-matching the internalized hypothesis `h` during a discharge attempt.
example (n : Nat) (h : ∀ x, 0 < g x) : f (f (g n)) = f (g n) := by
  sym =>
    simp fIdemGrind

-- Binder-introduced hypotheses are internalized per discharge attempt on top of the
-- shared internalized prefix (`h₁`).
/--
error: `sym` failed
case grind
n m : Nat
h₁ : 2 ≤ n
⊢ ∀ (h : n ≤ m), f m + p h = 0
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] 2 ≤ n
  [eqc] True propositions
    [prop] 2 ≤ n
-/
#guard_msgs in
example (n m : Nat) (h₁ : 2 ≤ n) : ∀ (h : n ≤ m), f (f m) + p h = 0 := by
  sym =>
    simp fIdemGrind
