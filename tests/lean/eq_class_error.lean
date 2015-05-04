inductive foo :=
| a | b

open foo

-- This test demonstrates we need to disable local instances.
set_option elaborator.local_instances false

definition decidable_eq_foo [instance] : ∀ f₁ f₂ : foo, decidable (f₁ = f₂)
| a  a := by left; reflexivity
| a  b := by right; contradiction
| b  a := by right; contradiction
-- If we don't disable the local_instances, then type class resolution synthesizes the term (decidable_eq_foo b b) which is not a
-- valid "recursive application", and the recursive equation compiler fails with a cryptic message saying we should try to use well-founded recursion.
| b  b := _
