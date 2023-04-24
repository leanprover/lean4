theorem exists_foo : ∃ T : Type, Nonempty T := ⟨Unit, ⟨()⟩⟩

example : True := by
  cases exists_foo
  rename_i T hT
  have : Nonempty T := inferInstance
  trivial
