def foo : Fin 5 :=
  let rec bla : 0 < 5 := by decide
  ⟨0, bla⟩
#print foo.bla
