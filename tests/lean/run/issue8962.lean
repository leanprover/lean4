-- This triggered a bug in the linear-size `noConfusionType` construction
-- which confused the kernel when producing the `noConfusion` lemma.

-- set_option debug.skipKernelTC true
set_option pp.universes true

-- Works

inductive S where
| a {α : Sort u} {β : Type v} (f : α → β)
| b

/--
info: @[reducible] protected def S.noConfusionType.withCtorType.{u_1, u, v} : Type u_1 → Nat → Type (max u u_1 (v + 1)) :=
fun P ctorIdx =>
  bif Nat.blt ctorIdx 1 then
    PULift.{max (u + 1) (u_1 + 1) (v + 2), max (max (u + 1) (u_1 + 1)) (v + 2)}
      ({α : Sort u} → {β : Type v} → (α → β) → P)
  else PULift.{max (u + 1) (u_1 + 1) (v + 2), u_1 + 1} P
-/
#guard_msgs in
#print S.noConfusionType.withCtorType

-- Didn't work

inductive T where
| a {α : Sort u} {β : Sort v} (f : α → β)
| b

/--
info: @[reducible] protected def T.noConfusionType.withCtorType.{u_1, u, v} : Type u_1 →
  Nat → Sort (max (u + 1) (u_1 + 1) (v + 1) (imax u v)) :=
fun P ctorIdx =>
  bif Nat.blt ctorIdx 1 then
    PULift.{max (u + 1) (u_1 + 1) (v + 1) (imax u v), max (max (max (u + 1) (u_1 + 1)) (v + 1)) (imax u v)}
      ({α : Sort u} → {β : Sort v} → (α → β) → P)
  else PULift.{max (u + 1) (u_1 + 1) (v + 1) (imax u v), u_1 + 1} P
-/
#guard_msgs in
#print T.noConfusionType.withCtorType
