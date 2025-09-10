open Option

theorem join_pmap_eq_pmap_join {p : α → Prop}  {f : ∀ a, p a → β} {x : Option (Option α)} (H) :
    (pmap (pmap f) x H).join = pmap f x.join fun a h ↦ H (some a) (mem_of_mem_join h) _ rfl := by
  -- There are two different equivalent classes containing `some (f val_1 ⋯)` (with different proof terms).
  -- Combining these would close the goal.
  grind [cases Option]
