import Lean.Meta.Sym
import Std.WP

/-!
`Sym.intros` and `Sym.simp` read the assigned type of a binder domain. `intro x` registers the
local instance `x : MyC c`, and `simp [fst_mk]` rewrites the domain `(a, b).fst = 0`.
-/

open Lean.Order Std.Internal.Order

class MyC (p : Prop) : Prop where
  out : p

example (c : Prop) : (True : Prop) ⊑ (MyC c → c) := by
  sym =>
    apply le_forall
    intro x
    tactic => exact fun _ => MyC.out

theorem fst_mk (a b : Nat) : (a, b).fst = a := rfl

example (a b : Nat) (P : Prop) (h : a = 0 → P) : (True : Prop) ⊑ ((a, b).fst = 0 → P) := by
  sym =>
    apply le_forall
    simp [fst_mk]
    intro x
    tactic => exact fun _ => h x
