class AddIdempotent (α : Type u) [Add α] : Prop where
  add_id (x : α) : x + x = x

export AddIdempotent (add_id)

theorem tst [Add α] [AddIdempotent α] (x : α) : id (x + x + x)  = x := by
  rw [add_id, add_id]
  simp [id]
