def foo.{u} {α : Type u} : α → α := by
  exact id.{u+1}
