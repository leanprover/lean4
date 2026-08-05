import Lean.Meta.Sym
import Std.Internal.Do

/-!
`Sym` discrimination-tree retrieval resolves assigned metavariables lazily.

`Pattern.unify?` creates the metavariables for pattern variables before solving pending
constraints, so subgoals returned by `Sym.BackwardRule.apply` can have stored types that
mention assigned metavariables. Here, after `apply le_of_forall_le` and `intro`, the goal's
stored carrier is such a metavariable. `le_pi_eq_forall`'s pattern requires an arrow in that
position; retrieval must follow the assignment to find the theorem, otherwise `Sym.simp`
fails with "made no progress". The matching layers below retrieval already resolve assigned
metavariables.
-/

open Lean.Order

example (f g : Nat → Nat → Prop) (h : ∀ a b, f a b ⊑ g a b) : f ⊑ g := by
  sym =>
    apply Lean.Order.le_of_forall_le
    intro a
    simp [Lean.Order.le_pi_eq_forall]
    tactic => exact h a
