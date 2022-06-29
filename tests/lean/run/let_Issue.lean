class C (α : Type)

instance : C (Fin (n+1)) := ⟨⟩

instance : C (Fin UInt64.size) :=
  let _ : C (Fin UInt64.size) := inferInstanceAs (C (Fin (_+1)))
  inferInstance
