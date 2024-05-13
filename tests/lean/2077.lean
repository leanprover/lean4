import Lean

noncomputable section
@[simp] def foo : Nat := 1
@[simp] noncomputable def bar : Nat := Classical.choice ⟨0⟩
@[simp] def baz : Nat := Classical.choice ⟨0⟩ -- `@[simp]` attribute doesn't get executed

open Lean Meta Elab Command

#eval liftCoreM <| do
  let x1 := simpExtension.getState (← getEnv) |>.toUnfoldThms.contains ``foo
  let x2 := simpExtension.getState (← getEnv) |>.toUnfoldThms.contains <| ``bar
  let x3 := simpExtension.getState (← getEnv) |>.toUnfoldThms.contains <| ``baz
  logInfo m!"{x1} {x2} {x3}" -- should not return: "true true false".
