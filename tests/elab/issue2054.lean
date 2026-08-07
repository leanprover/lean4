import Lean

open Lean Elab Tactic

elab "my_infer_instance" : tactic => do
  (← getMainGoal).inferInstance
  replaceMainGoal []

class Foo : Prop where
  trivial : True

instance : Foo := ⟨True.intro⟩

example : Foo := by
  my_infer_instance
