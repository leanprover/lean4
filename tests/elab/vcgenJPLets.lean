import Lean
import Std.Tactic.Do

set_option sym.debug true

open Std.WP
set_option experimental.vcgen true

/-!
`vcgen +jp` anti-unifies the arguments of the jumps to a join point through the `let` locals of
the branches. A reassignment `x := e` in a branch passes a `let` local with the value `e`.
-/

-- The values `s + 1` and `s + 2` of the `let` locals anti-unify to `s + z`.
def addOneOrTwo (o : Nat) : StateM Nat Unit := do
  let mut x ← get
  match o with
  | 0 => x := x + 1
  | _ => x := x + 2
  set x

/--
trace: case vc1
o s₀ s✝¹ : Nat
x✝¹ : PUnit
x✝ s✝ : Nat
h✝ : ∃ z, (x✝ = s₀ + z ∧ s✝ = s₀) ∧ (o = 0 ∧ z = 1 ∨ ∃ x, (x = 0 → False) ∧ o = x ∧ z = 2)
⊢ s₀ < x✝
-/
#guard_msgs in
example : ⦃fun s => s = s₀⦄ addOneOrTwo o ⦃fun _ s => s₀ < s⦄ := by
  vcgen +jp [addOneOrTwo]
  trace_state
  all_goals grind

-- The hole values `0` and `0 + 1` are in `simp` normal form in the hypothesis, so `simp` leaves the
-- binder domain of the join RHS unchanged.
def addZeroOrOne (c : Bool) : StateM Nat Unit := do
  let mut x ← get
  if c then x := x + 0 else x := x + (0 + 1)
  set x

/--
trace: case vc1
c : Bool
s₀ s✝¹ : Nat
x✝¹ : PUnit
x✝ s✝ : Nat
h✝ : ∃ z, (x✝ = s₀ + z ∧ s✝ = s₀) ∧ (c = true ∧ z = 0 ∨ ¬c = true ∧ z = 1)
⊢ s₀ ≤ x✝
-/
#guard_msgs in
example : ⦃fun s => s = s₀⦄ addZeroOrOne c ⦃fun _ s => s₀ ≤ s⦄ := by
  vcgen +jp [addZeroOrOne]
  trace_state
  all_goals grind

structure S where
  pc : Nat
  r : Nat

-- The values `s.r + 1` and `s.r * 2` of the `let` locals `r` have no common part, so the hole for
-- the field `r` takes the locals as its values. The field `pc` stays above the disjunction.
def addOrDouble (o : Nat) : StateM S Unit := do
  let mut s ← get
  match o with
  | 0 =>
    let r := s.r + 1
    s := { s with pc := s.pc + 4, r }
  | _ =>
    let r := s.r * 2
    s := { s with pc := s.pc + 4, r }
  set s

/--
trace: case vc1
o : Nat
s₀ s✝¹ : S
x✝¹ : PUnit
x✝ s✝ : S
h✝ :
  ∃ z,
    (x✝ = { pc := s₀.pc + 4, r := z } ∧ s✝ = s₀) ∧
      ((o = 0 ∧
          let r := s₀.r + 1;
          z = r) ∨
        ∃ x,
          (x = 0 → False) ∧
            o = x ∧
              let r := s₀.r * 2;
              z = r)
⊢ x✝.pc = s₀.pc + 4
-/
#guard_msgs in
example : ⦃fun s => s = s₀⦄ addOrDouble o ⦃fun _ s => s.pc = s₀.pc + 4⦄ := by
  vcgen +jp [addOrDouble]
  trace_state
  all_goals grind

-- Twelve `match`es that reassign a structure state. Each jump passes a `let` local of type `S`,
-- whose value agrees with the other jump on `pc`, so `grind` closes the goal without splitting
-- the `2¹²` combinations of alternatives.
def twelveMatches (b : Nat → Bool) : StateM S Unit := do
  let mut s ← get
  match b 0 with
  | true => s := { s with pc := s.pc + 4, r := s.r + 1 }
  | false => s := { s with pc := s.pc + 4, r := s.r + 2 }
  match b 1 with
  | true => s := { s with pc := s.pc + 4, r := s.r + 1 }
  | false => s := { s with pc := s.pc + 4, r := s.r + 2 }
  match b 2 with
  | true => s := { s with pc := s.pc + 4, r := s.r + 1 }
  | false => s := { s with pc := s.pc + 4, r := s.r + 2 }
  match b 3 with
  | true => s := { s with pc := s.pc + 4, r := s.r + 1 }
  | false => s := { s with pc := s.pc + 4, r := s.r + 2 }
  match b 4 with
  | true => s := { s with pc := s.pc + 4, r := s.r + 1 }
  | false => s := { s with pc := s.pc + 4, r := s.r + 2 }
  match b 5 with
  | true => s := { s with pc := s.pc + 4, r := s.r + 1 }
  | false => s := { s with pc := s.pc + 4, r := s.r + 2 }
  match b 6 with
  | true => s := { s with pc := s.pc + 4, r := s.r + 1 }
  | false => s := { s with pc := s.pc + 4, r := s.r + 2 }
  match b 7 with
  | true => s := { s with pc := s.pc + 4, r := s.r + 1 }
  | false => s := { s with pc := s.pc + 4, r := s.r + 2 }
  match b 8 with
  | true => s := { s with pc := s.pc + 4, r := s.r + 1 }
  | false => s := { s with pc := s.pc + 4, r := s.r + 2 }
  match b 9 with
  | true => s := { s with pc := s.pc + 4, r := s.r + 1 }
  | false => s := { s with pc := s.pc + 4, r := s.r + 2 }
  match b 10 with
  | true => s := { s with pc := s.pc + 4, r := s.r + 1 }
  | false => s := { s with pc := s.pc + 4, r := s.r + 2 }
  match b 11 with
  | true => s := { s with pc := s.pc + 4, r := s.r + 1 }
  | false => s := { s with pc := s.pc + 4, r := s.r + 2 }
  set s

example : ⦃fun s => s = s₀⦄ twelveMatches b ⦃fun _ s => s.pc = s₀.pc + 48⦄ := by
  vcgen +jp [twelveMatches]
  all_goals grind
