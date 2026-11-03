import Lean
import Std.Tactic.Do
open Std.WP
set_option experimental.vcgen true

/-!
Regression test for #16122: `vcgen +jp` produces goals with one disjunction per join point.
`lia` asserts the hull of each disjunction instead of splitting on it, so it solves them in time
linear in the number of joins.
-/

/-- `n` sequential `if`s, each adding 1 or 2 to the state. -/
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
            if $b $idx then modify (· + 1) else modify (· + 2)
            $rest:term)
    go 0 n.getNat

example (b : Nat → Bool) (s₀ : Nat) :
    ⦃fun s => s = s₀⦄ (diamonds% 8 b : StateM Nat Unit)
    ⦃fun _ s => s₀ + 8 ≤ s ∧ s ≤ s₀ + 16⦄ := by
  vcgen +jp
  all_goals lia

-- `lia` used to fail here after reaching the `splits` threshold, and `omega` exceeds the default
-- heartbeat limit.
example (b : Nat → Bool) (s₀ : Nat) :
    ⦃fun s => s = s₀⦄ (diamonds% 12 b : StateM Nat Unit)
    ⦃fun _ s => s₀ + 12 ≤ s ∧ s ≤ s₀ + 24⦄ := by
  vcgen +jp
  all_goals lia

example (b : Nat → Bool) (s₀ : Nat) :
    ⦃fun s => s = s₀⦄ (diamonds% 20 b : StateM Nat Unit)
    ⦃fun _ s => s₀ + 20 ≤ s ∧ s ≤ s₀ + 40⦄ := by
  vcgen +jp
  all_goals lia
