import Lean

/-!
# Porting Rocq `match goal` tactics with `expr` quotations

Each tactic below is a small, self-contained port of a classic Ltac `match goal` idiom, written
with `` `(expr| ...) `` patterns over hypotheses and targets:

- `chain_mp`: two-hypothesis modus ponens via nested `firstHyp` with `except` and a `$P` pin;
- `split_ands`: `for case` over `localHypTypes`, building projections with term templates;
- `clear_refl`: non-linear `?a = $a` patterns plus wildcards;
- `inst_forall t`: higher-order `∀ x, ?P x` patterns, instantiated by beta-reduction;
- `close_by_let`: `localHypDecls` and a local `[+$x]` unfold item for `let`-bound locals;
- `try_hyps`: backtracking `MVarId.firstHyp` whose arms mutate the goal before failing.
-/

namespace MatchGoalTactics
open Lean Meta Elab Tactic

/-- `chain_mp`: from `h₁ : P` and `h₂ : P → Q`, close `⊢ Q` (newest hypotheses first). -/
elab "chain_mp" : tactic => do
  let goal ← getMainGoal
  firstHyp fun h₁ P => do
    firstHyp (except := [h₁]) fun h₂ ty₂ => do
      -- `$P` pins the antecedent to the type of the first hypothesis.
      let `(expr/reducible| $P → ?Q) := ty₂ | failure
      unless ← isDefEq Q (← goal.getType) do failure
      goal.assign (mkApp h₂ h₁)
      replaceMainGoal []

example (p q r : Prop) : q → p → (p → q → r) → (q → r) → r := by
  intros
  chain_mp

/-- `split_ands`: replace every hypothesis `h : a ∧ b` by its two projections. -/
elab "split_ands" : tactic => withMainContext do
  let mut goal ← getMainGoal
  for case (h, `(expr| ?a ∧ ?b)) in (← localHypTypes) do
    -- Term templates: splices are checked against `a ∧ b` and instances are resolved statically.
    let (_, g) ← goal.note `left (← `(expr| And.left ($h : $a ∧ $b))) a
    let (_, g) ← g.note `right (← `(expr| And.right ($h : $a ∧ $b))) b
    goal ← g.clear h.fvarId!
  replaceMainGoal [goal]

example (p q r : Prop) (h : p ∧ q) (h' : q ∧ r) : r ∧ p := by
  split_ands
  exact ⟨by assumption, by assumption⟩

/-- `clear_refl`: drop trivial equations `h : a = a` (the second `$a` is a non-linear pin). -/
elab "clear_refl" : tactic => withMainContext do
  let mut goal ← getMainGoal
  for case (h, `(expr| (?a : _) = $a)) in (← localHypTypes) do
    goal ← goal.clear h.fvarId!
  replaceMainGoal [goal]

example (n : Nat) : n = n → n + 1 = n + 1 → n = 0 → n = 0 := by
  intro h₁ h₂ h₃
  clear_refl
  fail_if_success exact h₁
  fail_if_success exact h₂
  exact h₃

/-- `inst_forall t`: for every `h : ∀ x : Nat, P x`, add `h t : P t` (beta-reduced). -/
elab "inst_forall " t:term : tactic => withMainContext do
  let t ← Term.elabTerm t (mkConst ``Nat)
  let mut goal ← getMainGoal
  for case (h, `(expr| ∀ x : Nat, ?P x)) in (← localHypTypes) do
    -- `?P` is captured as a lambda `fun x => ...`; `headBeta` instantiates it with `t`.
    goal := (← goal.note `inst (mkApp h t) (mkApp P t).headBeta).2
  replaceMainGoal [goal]

example (f : Nat → Nat) (hf : ∀ x : Nat, f x = x + 1) : f 2 = 3 := by
  inst_forall 2
  assumption

/-- `close_by_let`: close `⊢ a = b` when `b` matches `a` after unfolding one `let` local. -/
elab "close_by_let" : tactic => withMainContext do
  let goal ← getMainGoal
  let `(expr| (?a : _) = ?b) ← getMainTarget | throwError "close_by_let: not an equation"
  for case (x, _, some _) in (← localHypDecls (reverse := true)) do
    -- `[+$x]` lets the structural matcher unfold exactly the local definition `x`.
    if let `(expr/structural[+$x]| $a) := b then
      goal.refl
      replaceMainGoal []
      return
  throwError "close_by_let: no `let` local makes both sides agree"

example (n : Nat) : let k := n + 1; k = n + 1 := by
  intro k
  close_by_let

/--
`try_hyps`: newest-first backtracking over implications `h : A → B`. Each arm applies `h`
(mutating the goal) and then insists the new goal is closed by `assumption`; `MVarId.firstHyp`
rolls a failing arm back atomically before trying the next hypothesis, like Rocq's `match goal`.
-/
elab "try_hyps" : tactic => do
  let goal ← getMainGoal
  goal.firstHyp fun h ty => do
    let `(expr/reducible| ?_ → _) := ty | failure
    let [g] ← goal.apply h | failure
    g.assumption
  replaceMainGoal []

-- `hqr` is tried first and its `apply` leaves the unprovable goal `q`, so it is rolled back.
example (p q r : Prop) : p → (p → r) → (q → r) → r := by
  intros
  try_hyps

end MatchGoalTactics
