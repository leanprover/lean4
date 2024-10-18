/-!
This test checks that simp is able to instantiate the parameter `g` below. It does not
appear on the lhs of the rule, but solving `hf` fully determines it.
-/

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


-- An example with zipWith

theorem zipWith_ignores_right
  (l₁ : List α) (l₂ : List β) (f : α → β → γ) (g : α → γ)
  (h : ∀ a b, f a b = g a) :
  List.zipWith f l₁ l₂ = List.map g (l₁.take l₂.length) := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons x xs ih =>
    cases l₂
    · simp
    · simp [List.zipWith, h, ih]

example (l₁ l₂ : List Nat) (hlen: l₁.length = l₂.length):
  List.zipWith (fun x y => x*x) l₁ l₂ = l₁.map (fun x => x * x) := by
  simp only [zipWith_ignores_right, hlen.symm, List.take_length]
