import Std.WP

/-!
`vcgen` reads the assigned type of the state binder of a frame goal, so it splits the pair state
into its components and states the verification condition on them.
-/

open Lean Order Std WP
set_option experimental.vcgen true

@[irreducible] def bumpFst : StateM (Nat × Nat) Unit := modify fun s => (s.1 + 1, s.2)

/--
trace: case vc1
F P : Nat × Nat → Prop
a✝¹ b✝ : Nat
a✝ : F (a✝¹, b✝)
⊢ F (a✝¹ + 1, b✝)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example {F P : Nat × Nat → Prop} : WP.Frames meet bumpFst F P := by
  refine WP.frames_of_conjunctive (PartialOrder.rel_trans (meet_le_right _ _) ?_)
    (fun _ => meet_le_right _ _)
  vcgen [bumpFst]
  trace_state
  all_goals sorry

example {F P : Nat × Nat → Prop} (h : ∀ a b, F (a, b) = F (0, b)) : WP.Frames meet bumpFst F P := by
  refine WP.frames_of_conjunctive (PartialOrder.rel_trans (meet_le_right _ _) ?_)
    (fun _ => meet_le_right _ _)
  vcgen [bumpFst] with finish
