theorem ex [Add α]
            (assoc : {a b c : α} → a + b + c = a + (b + c))
            (comm  : {a b : α} → a + b = b + a)
            (f : α → α) (x y z : α) : f (x + (y + z)) = f (y + (x + z)) := by
  let leftAssoc {a b c : α} : a + (b + c) = b + (a + c) := by
    rw [← assoc, comm (a := a), assoc]
  simp [leftAssoc]
