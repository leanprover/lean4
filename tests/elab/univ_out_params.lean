import Lean

open Lean Meta

@[univ_out_params v]
class ToLvl₁.{u, v} : Type where
  dummy : ∀ (_ : Sort u) (_ : Sort v), True := fun _ _ => trivial

/-- info: (some #[1]) -/
#guard_msgs in
run_meta do IO.println <| getOutLevelParamPositions? (← getEnv) ``ToLvl₁

@[univ_out_params]
class ToLvl₂.{u, v} : Type where
  dummy : ∀ (_ : Sort u) (_ : Sort v), True := fun _ _ => trivial

/-- info: (some #[]) -/
#guard_msgs in
run_meta do IO.println <| getOutLevelParamPositions? (← getEnv) ``ToLvl₂

@[univ_out_params v u]
class ToLvl₃.{u, v} : Type where
  dummy : ∀ (_ : Sort u) (_ : Sort v), True := fun _ _ => trivial

/-- info: (some #[0, 1]) -/
#guard_msgs in
run_meta do IO.println <| getOutLevelParamPositions? (← getEnv) ``ToLvl₃

/-- error: `v` is not a universe parameter of `Foo` -/
#guard_msgs in
@[univ_out_params v]
class Foo (α : Type u) where
  a : α

/-- error: invalid `univ_out_params`, `Bla` is not a class -/
#guard_msgs in
@[univ_out_params u]
structure Bla (α : Type u) where
  a : α
