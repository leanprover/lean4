theorem subtype_inj (A: Type) (p: A → Prop) (a b: A) (pa: p a) (pb: p b) : (⟨a, pa⟩: {a//p a}) = (⟨b, pb⟩: {b//p b}) → a = b := by
  intro eq
  injection eq
  assumption
