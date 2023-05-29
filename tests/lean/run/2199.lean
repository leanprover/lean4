theorem exists_foo : ∃ T : Type, Nonempty T := ⟨Unit, ⟨()⟩⟩

set_option trace.Meta.debug true
example : True := by
  cases exists_foo
  rename_i T hT
  have : Nonempty T := inferInstance
  trivial
