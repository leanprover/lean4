/-!
This test checks that simp is able to instantiate the parameter `g` below. It does not
appear on the lhs of the rule, but solving `hf` fully determines it.
-/

theorem List.foldl_subtype (p : α → Prop) (l : List (Subtype p)) (f : β → Subtype p → β)
  (g : β → α → β) (b : β)
  {hf : ∀ b x h, f b ⟨x, h⟩ = g b x} :
    l.foldl f b = (l.map (·.val)).foldl g b := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simp [hf, ih]

example (l : List Nat)  :
  l.attach.foldl (fun acc t => max acc (t.val)) 0 = l.foldl (fun acc t => max acc t) 0 := by
  simp [List.foldl_subtype]

example (l : List Nat)  :
  l.attach.foldl (fun acc ⟨t, _⟩ => max acc t) 0 = l.foldl (fun acc t => max acc t) 0 := by
  simp [List.foldl_subtype]
