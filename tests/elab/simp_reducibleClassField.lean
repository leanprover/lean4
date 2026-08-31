set_option backward.whnf.reducibleClassField true in
example [Ord α] {a b : α} :
    (letI : Ord α := ⟨fun a b => compare b a⟩; compare a b) = compare b a := by
  simp only

set_option backward.whnf.reducibleClassField true in
example [Ord α] {a b : α} :
    (letI : Ord α := ⟨fun a b => compare b a⟩; compare a b) = compare b a := by
  simp
