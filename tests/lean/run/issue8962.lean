-- This triggered a bug in the linear-size `noConfusionType` construction
-- which confused the kernel when producing the `noConfusion` lemma.

set_option debug.skipKernelTC true
set_option pp.universes true

-- Works

inductive S where
| a {α : Sort u} {β : Type v} (f : α → β)
| b

/--
info: @[reducible] protected def S.noConfusionType.withCtorType.{u_1, u, v} : Type u_1 →
  Nat → Type (max (max u (v + 1)) u_1) :=
fun P ctorIdx =>
  bif Nat.blt ctorIdx 1 then
    ULift.{max (max u (v + 1)) u_1, max (max u u_1) (v + 1)} ({α : Sort u} → {β : Type v} → (α → β) → P)
  else ULift.{max (max u (v + 1)) u_1, u_1} P
-/
#guard_msgs in
#print S.noConfusionType.withCtorType

-- Doesn't work yet:

/--
error: invalid universe level, max (max (max (u+1) (u_1+1)) (v+1)) (imax u v) is not greater than 0
-/
#guard_msgs in
inductive T where
| a {α : Sort u} {β : Sort v} (f : α → β)
| b

/-- error: unknown constant 'T.noConfusionType.withCtorType' -/
#guard_msgs in
#print T.noConfusionType.withCtorType
