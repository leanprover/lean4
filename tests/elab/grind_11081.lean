namespace List

protected def diff {α} [BEq α] : List α → List α → List α
  | l, [] => l
  | l₁, a :: l₂ => if l₁.elem a then List.diff (l₁.erase a) l₂ else List.diff l₁ l₂

def Subperm (l₁ l₂ : List α) : Prop := ∃ l, l ~ l₁ ∧ l <+ l₂

open Perm (swap)

theorem Perm.subperm_left {l l₁ l₂ : List α} (p : l₁ ~ l₂) : Subperm l l₁ ↔ Subperm l l₂ :=
  sorry

theorem Sublist.subperm {l₁ l₂ : List α} (s : l₁ <+ l₂) : Subperm l₁ l₂ := sorry

theorem Subperm.perm_of_length_le {l₁ l₂ : List α} :
    Subperm l₁ l₂ → length l₂ ≤ length l₁ → l₁ ~ l₂ :=
  sorry

end List

variable {α : Type} [DecidableEq α] {l₁ l₂ : List α}

open List

/--
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
theorem countP_diff (hl : Subperm l₂ l₁) (p : α → Bool) :
    countP p l₁ = countP p (l₁.diff l₂ ++ l₂) := by
  grind -verbose [
    List.Perm.subperm_left,
    List.Sublist.subperm,
    List.Subperm.perm_of_length_le,
    List.Perm.countP_congr,
    List.countP_eq_length_filter
  ]
