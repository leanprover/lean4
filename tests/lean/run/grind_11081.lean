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
case grind.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1
α : Type
inst : DecidableEq α
l₁ l₂ : List α
hl : l₂.Subperm l₁
p : α → Bool
h : ¬countP p l₁ = countP p (l₁.diff l₂ ++ l₂)
w : α
h_2 : ¬count w (l₁.diff l₂ ++ l₂) = count w l₁
w_1 : α
h_4 : ¬count w_1 l₁ = count w_1 (l₁.diff l₂ ++ l₂)
left : l₂ ⊆ l₁
right : ∀ {a : α}, a ∈ l₂ → a ∈ l₁
left_1 : filter p l₂ <+ filter p l₁
w_2 : List α
left_2 : w_2 <+ l₁
right_2 : filter p l₂ = filter p w_2
w_3 : List α
left_3 : w_3 <+ l₁
right_3 : filter p l₂ = filter p w_3
left_4 : l₁.diff l₂ ~ l₁
right_4 : ∀ (a : α), count a (l₁.diff l₂) = count a l₁
w_4 : α
h_11 : ¬count w_4 (l₁.diff l₂ ++ l₂) = count w_4 (l₁.diff l₂)
w_5 : α
h_13 : ¬count w_5 (l₁.diff l₂) = count w_5 (l₁.diff l₂ ++ l₂)
left_5 : l₁.diff l₂ ~ l₂
right_5 : ∀ (a : α), count a (l₁.diff l₂) = count a l₂
w_6 : α
h_16 : ¬count w_6 (l₁.diff l₂ ++ l₂) = count w_6 l₂
w_7 : α
h_18 : ¬count w_7 l₂ = count w_7 (l₁.diff l₂ ++ l₂)
left_6 : l₂ ~ l₁
right_6 : ∀ (a : α), count a l₂ = count a l₁
left_7 : l₂ ~ l₁.diff l₂
right_7 : ∀ (a : α), count a l₂ = count a (l₁.diff l₂)
left_8 : l₁ ~ l₁.diff l₂
right_8 : ∀ (a : α), count a l₁ = count a (l₁.diff l₂)
left_9 : l₁ ~ l₂
right_9 : ∀ (a : α), count a l₁ = count a l₂
left_10 : filter p l₁ ~ filter p (l₁.diff l₂ ++ l₂)
right_10 : ∀ (a : α), count a (filter p l₁) = count a (filter p (l₁.diff l₂ ++ l₂))
left_11 : filter p (l₁.diff l₂ ++ l₂) ~ filter p l₁
right_11 : ∀ (a : α), count a (filter p (l₁.diff l₂ ++ l₂)) = count a (filter p l₁)
left_12 : l₁.diff l₂ ++ l₂ ~ l₁.diff l₂ ++ (l₁.diff l₂ ++ l₂)
right_12 : ∀ (a : α), count a (l₁.diff l₂ ++ l₂) = count a (l₁.diff l₂ ++ (l₁.diff l₂ ++ l₂))
left_13 : l₁.diff l₂ ++ l₂ ~ l₂ ++ (l₁.diff l₂ ++ l₂)
right_13 : ∀ (a : α), count a (l₁.diff l₂ ++ l₂) = count a (l₂ ++ (l₁.diff l₂ ++ l₂))
left_14 : l₁.diff l₂ ++ l₂ ~ l₁.diff l₂ ++ l₂ ++ l₁
right_14 : ∀ (a : α), count a (l₁.diff l₂ ++ l₂) = count a (l₁.diff l₂ ++ l₂ ++ l₁)
left_15 : l₁.diff l₂ ++ l₂ ~ l₁.diff l₂ ++ l₂ ++ (l₁.diff l₂ ++ l₂)
right_15 : ∀ (a : α), count a (l₁.diff l₂ ++ l₂) = count a (l₁.diff l₂ ++ l₂ ++ (l₁.diff l₂ ++ l₂))
left_16 : l₁.diff l₂ ++ l₂ ~ l₁.diff l₂ ++ l₂ ++ l₂
right_16 : ∀ (a : α), count a (l₁.diff l₂ ++ l₂) = count a (l₁.diff l₂ ++ l₂ ++ l₂)
left_17 : l₁.diff l₂ ++ l₂ ~ l₁.diff l₂ ++ l₂ ++ l₁.diff l₂
right_17 : ∀ (a : α), count a (l₁.diff l₂ ++ l₂) = count a (l₁.diff l₂ ++ l₂ ++ l₁.diff l₂)
left_18 : l₁.diff l₂ ++ l₂ ~ l₁ ++ (l₁.diff l₂ ++ l₂)
right_18 : ∀ (a : α), count a (l₁.diff l₂ ++ l₂) = count a (l₁ ++ (l₁.diff l₂ ++ l₂))
left_19 : filter p (l₁.diff l₂ ++ l₂) ~ filter p (l₁.diff l₂)
right_19 : ∀ (a : α), count a (filter p (l₁.diff l₂ ++ l₂)) = count a (filter p (l₁.diff l₂))
left_20 : filter p (l₁.diff l₂) ~ filter p (l₁.diff l₂ ++ l₂)
right_20 : ∀ (a : α), count a (filter p (l₁.diff l₂)) = count a (filter p (l₁.diff l₂ ++ l₂))
left_21 : (filter p (l₁.diff l₂ ++ l₂)).Subperm (filter p l₁)
right_21 : (filter p (l₁.diff l₂ ++ l₂)).Subperm (filter p (l₁.diff l₂ ++ l₂))
left_22 : l₁.diff l₂ ++ l₂ ++ l₁.diff l₂ ~ l₁.diff l₂ ++ l₂
right_22 : ∀ (a : α), count a (l₁.diff l₂ ++ l₂ ++ l₁.diff l₂) = count a (l₁.diff l₂ ++ l₂)
left_23 : l₁.diff l₂ ++ l₂ ++ l₁ ~ l₁.diff l₂ ++ l₂
right_23 : ∀ (a : α), count a (l₁.diff l₂ ++ l₂ ++ l₁) = count a (l₁.diff l₂ ++ l₂)
left_24 : l₁.diff l₂ ++ l₂ ++ l₂ ~ l₁.diff l₂ ++ l₂
right_24 : ∀ (a : α), count a (l₁.diff l₂ ++ l₂ ++ l₂) = count a (l₁.diff l₂ ++ l₂)
left_25 : l₁.diff l₂ ++ l₂ ++ (l₁.diff l₂ ++ l₂) ~ l₁.diff l₂ ++ l₂
right_25 : ∀ (a : α), count a (l₁.diff l₂ ++ l₂ ++ (l₁.diff l₂ ++ l₂)) = count a (l₁.diff l₂ ++ l₂)
left_26 : l₁ ++ (l₁.diff l₂ ++ l₂) ~ l₁.diff l₂ ++ l₂
right_26 : ∀ (a : α), count a (l₁ ++ (l₁.diff l₂ ++ l₂)) = count a (l₁.diff l₂ ++ l₂)
left_27 : l₂ ++ (l₁.diff l₂ ++ l₂) ~ l₁.diff l₂ ++ l₂
right_27 : ∀ (a : α), count a (l₂ ++ (l₁.diff l₂ ++ l₂)) = count a (l₁.diff l₂ ++ l₂)
left_28 : l₁.diff l₂ ++ (l₁.diff l₂ ++ l₂) ~ l₁.diff l₂ ++ l₂
right_28 : ∀ (a : α), count a (l₁.diff l₂ ++ (l₁.diff l₂ ++ l₂)) = count a (l₁.diff l₂ ++ l₂)
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
