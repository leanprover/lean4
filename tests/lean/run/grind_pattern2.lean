def Set (α : Type) := α → Bool

def insertElem [DecidableEq α] (s : Set α) (a : α) : Set α :=
  fun x => a = x || s x

def contains (s : Set α) (a : α) : Bool :=
  s a

theorem contains_insert [DecidableEq α] (s : Set α) (a : α) : contains (insertElem s a) a := by
  simp [contains, insertElem]

grind_pattern contains_insert => contains (insertElem s a) a

-- TheoremPattern activation test

set_option trace.grind.pattern true

/--
warning: declaration uses 'sorry'
---
info: [grind.pattern] activated `contains_insert`
-/
#guard_msgs in
example [DecidableEq α] (s₁ s₂ : Set α) (a₁ a₂ : α) :
        s₂ = insertElem s₁ a₁ → a₁ = a₂ → contains s₂ a₂ := by
  fail_if_success grind
  sorry

/--
warning: declaration uses 'sorry'
---
info: [grind.pattern] reinsert `contains_insert`
[grind.pattern] activated `contains_insert`
-/
#guard_msgs in
example [DecidableEq α] (s₁ s₂ : Set α) (a₁ a₂ : α) :
        ¬ contains s₂ a₂ → s₂ = insertElem s₁ a₁ → a₁ = a₂ → False := by
  fail_if_success grind
  sorry
