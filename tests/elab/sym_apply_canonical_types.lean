import Lean.Meta.Sym
import Std.WP

/-!
`sym => apply` returns subgoals whose binder domains carry the assignments that the pending
constraints of the unification made. `simp` rewrites such a domain, and `intro` declares the
bound variable with it.
-/

open Lean.Order Std.Internal.Order

theorem fst_mk (a b : Nat) : (a, b).fst = a := rfl

example (a b : Nat) (P : Prop) (h : a = 0 → P) : (True : Prop) ⊑ ((a, b).fst = 0 → P) := by
  sym =>
    apply le_forall
    simp [fst_mk]
    intro x
    tactic => exact fun _ => h x
