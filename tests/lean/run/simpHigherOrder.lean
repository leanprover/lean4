/-!
This test checks that simp is able to instantiate the parameter `g` below. It does not
appear on the lhs of the rule, but solving `hf` fully determines it.
-/

theorem List.foldl_subtype (p : α → Prop) (l : List (Subtype p)) (f : β → Subtype p → β)
  (g : β → α → β) (b : β)
  (hf : ∀ b x h, f b ⟨x, h⟩ = g b x) :
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


theorem foldr_to_sum (l : List Nat) (f : Nat → Nat → Nat) (g : Nat → Nat)
  (h : ∀ acc x, f x acc = g x + acc) :
  l.foldr f 0 = Nat.sum (l.map g) := by
  rw [Nat.sum, List.foldr_map]
  congr
  funext x acc
  apply h

-- this works:
example (l : List Nat) :
  l.foldr (fun x a => x*x + a) 0 = Nat.sum (l.map (fun x => x * x)) := by
  simp [foldr_to_sum]

-- this does not, so such a pattern is still quite fragile

/-- error: simp made no progress -/
#guard_msgs in
example (l : List Nat) :
  l.foldr (fun x a => a + x*x) 0 = Nat.sum (l.map (fun x => x * x)) := by
  simp [foldr_to_sum]

-- but with stronger simp normal forms, it would work:

@[simp]
theorem add_eq_add_cancel (a x y : Nat) : (a + x = y + a) ↔  (x = y) := by omega

example (l : List Nat) :
  l.foldr (fun x a => a + x*x) 0 = Nat.sum (l.map (fun x => x * x)) := by
  simp [foldr_to_sum]
