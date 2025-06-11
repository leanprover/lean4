open List

theorem eraseP_eq_nil_iff {xs : List α} {p : α → Bool} : xs.eraseP p = [] ↔ xs = [] ∨ ∃ x, p x ∧ xs = [x] := by
  induction xs with grind

theorem eraseP_ne_nil_iff {xs : List α} {p : α → Bool} : xs.eraseP p ≠ [] ↔ xs ≠ [] ∧ ∀ x, p x → xs ≠ [x] := by
  induction xs with grind

theorem length_eraseP_of_mem (al : a ∈ l) (pa : p a) :
    length (l.eraseP p) = length l - 1 := by
  grind

-- reverse direction of lemma from library
theorem eraseP_filterMap' {f : α → Option β} {l : List α} :
    filterMap f (l.eraseP (fun x => match f x with | some y => p y | none => false)) = (filterMap f l).eraseP p := by
  grind

theorem eraseP_append_left {a : α} (pa : p a) {l₁ : List α} {l₂} : a ∈ l₁ → (l₁ ++ l₂).eraseP p = l₁.eraseP p ++ l₂ := by
  grind

theorem eraseP_append_right {l₁ : List α} {l₂} (h : ∀ b ∈ l₁, ¬p b) :
    eraseP p (l₁ ++ l₂) = l₁ ++ l₂.eraseP p := by
  grind
