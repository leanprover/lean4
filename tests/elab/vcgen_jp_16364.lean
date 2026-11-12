import Lean
import Std.Tactic.Do

set_option sym.debug true

open Std.WP
set_option experimental.vcgen true

/-!
Regression test for #16364: with a structure state, `vcgen +jp` states the fields that every jump
to a join point agrees on above the disjunction of the jumps, so `grind` closes the goals about
those fields without a case split.
-/

structure S where
  pc : Nat
  r : Nat

structure W where
  pc : BitVec 32
  r : BitVec 32

/-- `n` sequential `if`s. Both branches add 4 to `pc`, and they add 1 or 2 to `r`. -/
syntax "diamonds% " num term:max : term
macro_rules
  | `(diamonds% $n $b) => do
    let rec go (i k : Nat) : Lean.MacroM (Lean.TSyntax `term) := do
      match k with
      | 0 => `(pure ())
      | k + 1 =>
        let idx := Lean.Syntax.mkNumLit (toString i)
        let rest ← go (i + 1) k
        `(do
            if $b $idx then modify (fun s => { s with pc := s.pc + 4, r := s.r + 1 })
            else modify (fun s => { s with pc := s.pc + 4, r := s.r + 2 })
            $rest:term)
    go 0 n.getNat

/--
trace: case vc1
b : Nat → Bool
s₀ s✝¹ : S
x✝ : PUnit
s✝ : S
h✝ : ∃ z, s✝ = { pc := s₀.pc + 4, r := s₀.r + z } ∧ (b 0 = true ∧ z = 1 ∨ ¬b 0 = true ∧ z = 2)
⊢ s✝.pc = s₀.pc + 4
-/
#guard_msgs in
example (b : Nat → Bool) (s₀ : S) :
    ⦃fun s => s = s₀⦄ (diamonds% 1 b : StateM S Unit) ⦃fun _ s => s.pc = s₀.pc + 4⦄ := by
  vcgen +jp
  trace_state
  all_goals grind

example (b : Nat → Bool) (s₀ : S) :
    ⦃fun s => s = s₀⦄ (diamonds% 12 b : StateM S Unit) ⦃fun _ s => s.pc = s₀.pc + 48⦄ := by
  vcgen +jp
  all_goals grind

example (b : Nat → Bool) (s₀ : S) :
    ⦃fun s => s = s₀⦄ (diamonds% 12 b : StateM S Unit)
    ⦃fun _ s => s₀.r + 12 ≤ s.r ∧ s.r ≤ s₀.r + 24⦄ := by
  vcgen +jp
  all_goals grind

example (b : Nat → Bool) (s₀ : W) :
    ⦃fun s => s = s₀⦄ (diamonds% 12 b : StateM W Unit) ⦃fun _ s => s.pc = s₀.pc + 48⦄ := by
  vcgen +jp
  all_goals grind

-- Three jumps from a `match`: `pc` agrees at all of them.
def step (o : Option Nat) : StateM S Unit := do
  match o with
  | some 0 => modify fun s => { s with pc := s.pc + 4, r := 0 }
  | some n => modify fun s => { s with pc := s.pc + 4, r := n }
  | none => modify fun s => { s with pc := s.pc + 4 }
  modify fun s => { s with pc := s.pc + 4 }

example (s₀ : S) :
    ⦃fun s => s = s₀⦄ step o ⦃fun _ s => s.pc = s₀.pc + 8⦄ := by
  vcgen +jp [step]
  all_goals grind
