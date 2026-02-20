class AddIdepotent (α : Type u) [Add α] : Prop where
  add_id (x : α) : x + x = x

export AddIdepotent (add_id)

theorem tst [Add α] [AddIdepotent α] (x : α) : id (x + x + x)  = x := by
  rw [add_id, add_id]
  simp [id]
