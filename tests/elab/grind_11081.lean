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
error: `grind` failed
case grind.2.2.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1
α : Type
inst : DecidableEq α
l₁ l₂ : List α
hl : l₂.Subperm l₁
p : α → Bool
h : ¬countP p l₁ = countP p (l₁.diff l₂ ++ l₂)
left : ¬l₁.diff l₂ ++ l₂ ~ l₁
w : α
h_2 : ¬count w (l₁.diff l₂ ++ l₂) = count w l₁
w_1 : α
h_4 : ¬count w_1 (l₁.diff l₂ ++ l₂) = count w_1 l₁
left_1 : ¬l₁ ~ l₁.diff l₂ ++ l₂
w_2 : α
h_6 : ¬count w_2 l₁ = count w_2 (l₁.diff l₂ ++ l₂)
w_3 : α
h_8 : ¬count w_3 l₁ = count w_3 (l₁.diff l₂ ++ l₂)
left_2 : l₁.diff l₂ ~ l₁
right_2 : ∀ (a : α), count a (l₁.diff l₂) = count a l₁
left_3 : l₁.diff l₂ ~ l₁.diff l₂ ++ l₂
right_3 : ∀ (a : α), count a (l₁.diff l₂) = count a (l₁.diff l₂ ++ l₂)
left_4 : l₁.diff l₂ ~ l₂
right_4 : ∀ (a : α), count a (l₁.diff l₂) = count a l₂
left_5 : l₂ ~ l₁
right_5 : ∀ (a : α), count a l₂ = count a l₁
left_6 : l₂ ~ l₁.diff l₂ ++ l₂
right_6 : ∀ (a : α), count a l₂ = count a (l₁.diff l₂ ++ l₂)
left_7 : l₂ ~ l₁.diff l₂
right_7 : ∀ (a : α), count a l₂ = count a (l₁.diff l₂)
left_8 : l₁ ~ l₁.diff l₂
right_8 : ∀ (a : α), count a l₁ = count a (l₁.diff l₂)
left_9 : l₁.diff l₂ ++ l₂ ~ l₁.diff l₂
right_9 : ∀ (a : α), count a (l₁.diff l₂ ++ l₂) = count a (l₁.diff l₂)
left_10 : l₁ ~ l₂
right_10 : ∀ (a : α), count a l₁ = count a l₂
left_11 : l₁.diff l₂ ++ l₂ ~ l₂
right_11 : ∀ (a : α), count a (l₁.diff l₂ ++ l₂) = count a l₂
left_12 : filter p l₁ ~ filter p (l₁.diff l₂ ++ l₂)
right_12 : ∀ (a : α), count a (filter p l₁) = count a (filter p (l₁.diff l₂ ++ l₂))
left_13 : filter p (l₁.diff l₂ ++ l₂) ~ filter p l₁
right_13 : ∀ (a : α), count a (filter p (l₁.diff l₂ ++ l₂)) = count a (filter p l₁)
left_14 : l₂ ⊆ l₁
right_14 : ∀ {a : α}, a ∈ l₂ → a ∈ l₁
left_15 : filter p l₂ <+ filter p l₁
w_4 : List α
left_16 : w_4 <+ l₁
right_16 : filter p l₂ = filter p w_4
w_5 : List α
left_17 : w_5 <+ l₁
right_17 : filter p l₂ = filter p w_5
w_6 : List α
left_18 : w_6 <+ l₁.diff l₂ ++ l₂
right_18 : filter p l₂ = filter p w_6
w_7 : List α
left_19 : w_7 <+ l₁.diff l₂ ++ l₂
right_19 : filter p (l₁.diff l₂) = filter p w_7
left_20 : l₁.Subperm l₂
right_20 : l₁.Subperm (l₁.diff l₂ ++ l₂)
left_21 : (l₁.diff l₂ ++ l₂).Subperm (l₂ ++ (l₁.diff l₂ ++ l₂))
right_21 : (l₁.diff l₂ ++ l₂).Subperm (l₁ ++ (l₁.diff l₂ ++ l₂))
⊢ False
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
