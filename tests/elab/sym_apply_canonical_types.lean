import Lean.Meta.Sym
import Std.Internal.Do

/-!
`Sym.Pattern.unify?` instantiates assigned metavariables in the types of the fresh
metavariables it creates for pattern variables, so subgoals returned by
`Sym.BackwardRule.apply` are typed canonically with respect to the assignments made during
the application.

After `apply le_of_forall_le` and `intro`, the goal's carrier is the metavariable minted for
the rule's dependent codomain, assigned while processing pending constraints. `Sym.simp`
matches with `Pattern.match?`, which requires the carrier of `le_pi_eq_forall`'s left-hand
side syntactically; without canonical subgoal types this `simp` fails with
"`Sym.simp` made no progress".
-/

open Lean.Order

example (f g : Nat → Nat → Prop) (h : ∀ a b, f a b ⊑ g a b) : f ⊑ g := by
  sym =>
    apply Lean.Order.le_of_forall_le
    intro a
    simp [Lean.Order.le_pi_eq_forall]
    tactic => exact h a
