import Std.WP
open Std.WP Lean.Order

/-! The frame closure of a monadic interpretation, and the transport of its laws, accept a monad and
a resource type in universe 1 (#15424). -/

abbrev M := StateT (ULift.{1} Nat) Id
abbrev op : ULift.{1} Nat → (ULift.{1} Nat → Prop) → (ULift.{1} Nat → Prop) := FrameOp.ignore

@[instance_reducible] noncomputable def framed : MonadicWP M (ULift.{1} Nat → Prop) EStack⟨⟩ :=
  fun α => WP.withFrameClosure (Prog := M α) op inferInstance

example (α : Type 1) : @WP.IsMonotone (M α) α _ _ (framed α) _ _ :=
  MonadicWP.isMonotone_withFrameClosure (m := M) op α

example : @MonadicWP.IsLaxMonadMorphism M _ _ _ framed _ _ :=
  MonadicWP.isLaxMonadMorphism_withFrameClosure (m := M) op (comp := fun r _ => r) (e := ⟨0⟩)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
