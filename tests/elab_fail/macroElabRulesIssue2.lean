import Lean
open Lean Elab

declare_syntax_cat fixDecl
syntax ident : fixDecl
syntax ident "<" term : fixDecl

syntax "Fix₁ " fixDecl : tactic

elab_rules : tactic
  | `(tactic| Fix₁ $x:ident) => logInfo "simple"

elab_rules : tactic
  | `(tactic| Fix₁ $x:ident < $bound:term) =>
    throwError "Failed at elab_rules"

macro_rules
| `(ℕ) => `(Nat)

example : ∀ b : ℕ, ∀ a : Nat, a ≥ 2 → a / a = 1 := by
  Fix₁ b
  Fix₁ a < 2  -- should produce `Failed at elab_rules`
