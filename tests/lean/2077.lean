import Lean

noncomputable section
@[simp] def foo : Nat := 1
@[simp] noncomputable def bar : Nat := Classical.choice ⟨0⟩
@[simp] def baz : Nat := Classical.choice ⟨0⟩ -- `@[simp]` attribute doesn't get executed

open Lean Meta Elab Command

#eval liftCoreM <| do
  let x1 := simpExtension.getState (← getEnv) |>.toUnfold.contains <| ``foo
  let x2 := simpExtension.getState (← getEnv) |>.toUnfold.contains <| ``bar
  let x3 := simpExtension.getState (← getEnv) |>.toUnfold.contains <| ``baz
  logInfo m!"{x1} {x2} {x3}" -- should not return: "true true false".
