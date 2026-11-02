import Lean
import Std.Tactic.Do
open Std WP
set_option experimental.vcgen true

/-!
`vcgen` keeps the `have`s of a program, and `isDefEqS` compares them structurally. `vcgen +jp [f]`
uses `f.eq_def` for a non-recursive `f` whose `f.eq_n` zeta-reduce a join point (#16122).
-/

elab "goal_count" : tactic => do
  Lean.logInfo m!"{(← Lean.Elab.Tactic.getGoals).length} goals"

def diamonds (b : Nat → Bool) : StateM Nat Unit := do
  if b 0 then modify (· + 1) else modify (· + 2)
  if b 1 then modify (· + 1) else modify (· + 2)
  if b 2 then modify (· + 1) else modify (· + 2)

/-- info: 4 goals -/
#guard_msgs in
example (b : Nat → Bool) (s₀ : Nat) :
    ⦃fun s => s = s₀⦄ diamonds b ⦃fun _ s => s₀ + 3 ≤ s ∧ s ≤ s₀ + 6⦄ := by
  vcgen +jp [diamonds]
  goal_count
  all_goals lia

/-- info: 16 goals -/
#guard_msgs in
example (b : Nat → Bool) (s₀ : Nat) :
    ⦃fun s => s = s₀⦄ diamonds b ⦃fun _ s => s₀ + 3 ≤ s ∧ s ≤ s₀ + 6⦄ := by
  vcgen [diamonds]
  goal_count
  all_goals lia

-- The join point precedes a root `match`, so `rootMatch.eq_n` would zeta-reduce it.
def rootMatch (x : Nat) (b : Bool) : StateM Nat Nat := do
  let mut y := 0
  match x with
  | 0 => y := 1
  | _ => if b then y := 2 else y := 3
  let s ← get
  return y + s

/-- info: 1 goals -/
#guard_msgs in
example (x : Nat) (b : Bool) : ⦃fun _ => True⦄ rootMatch x b ⦃fun r _ => r > 0⦄ := by
  vcgen +jp [rootMatch]
  goal_count
  all_goals grind

structure M where
  x : Nat
  y : Nat

structure St where
  m : M
  b : Nat

-- The struct update elaborates to `have __src := s.m; …` in an argument of `modify`.
def setX (k : Nat) : StateM St Unit :=
  modify fun s => { s with m := { s.m with x := k } }

theorem setX_spec (s₀ : St) (k : Nat) :
    ⦃fun s => s = s₀⦄ setX k ⦃fun _ s' => s'.m = { x := k, y := s₀.m.y }⦄ := by
  vcgen [setX] with finish

-- The postcondition elaborates to `let __src := s₀.m; …`.
example (s₀ : St) (k : Nat) :
    ⦃fun s => s = s₀⦄ setX k ⦃fun _ s' => s'.m = { s₀.m with x := k }⦄ := by
  vcgen [setX] with finish

-- `isDefEqS` compares a `have` structurally: a `have` against any other term is not defeq.
/-- error: `apply` failed, rule is not applicable -/
#guard_msgs in
example (n : Nat) : (have t := n; t + 1) = n + 1 := by
  sym =>
    apply Eq.refl

/-- error: `apply` failed, rule is not applicable -/
#guard_msgs in
example (n m : Nat) (h : n = m) : (have t := n; t + 1) = (have t := m; t + 1) := by
  sym =>
    apply Eq.refl
