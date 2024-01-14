inductive ListSplit {α : Type u} : List α → Type u
  | split l₁ l₂ : ListSplit (l₁ ++ l₂)

def splitList {α : Type _} : (l : List α) → ListSplit l
  | [] => ListSplit.split [] []
  | h :: t => ListSplit.split [h] t

theorem Nat.lt_add_left {m n : Nat}  : m < n + m := sorry
theorem Nat.lt_add_right {m n : Nat} : m < m + n := sorry

def len : List α → Nat
  | [] => 0
  | a :: [] => 1
  | l =>
    match splitList l with
    | ListSplit.split fst snd => len fst + len snd
termination_by l => l.length
decreasing_by
  all_goals
  simp [measure, id, invImage, InvImage, Nat.lt_wfRel, WellFoundedRelation.rel, sizeOf] <;>
  first
    | apply Nat.lt_add_right
    | apply Nat.lt_add_left

theorem len_nil : len ([] : List α) = 0 := by
  simp [len]

-- The `simp [len]` above generated the following equation theorems for len
#check @len._eq_1
#check @len._eq_2
#check @len._eq_3 -- It is conditional, and may be tricky to use.

theorem len_1 (a : α) : len [a] = 1 := by
  simp [len]

theorem len_2 (a b : α) (bs : List α) : len (a::b::bs) = 1 + len (b::bs) := by
  conv => lhs; unfold len

-- The `unfold` tactic above generated the following theorem
#check @len._unfold

theorem len_cons (a : α) (as : List α) : len (a::as) = 1 + len as := by
  cases as with
  | nil => simp [len_1, len_nil]
  | cons b bs => simp [len_2]

theorem listlen : ∀ l : List α, l.length = len l := by
  intro l
  induction l with
  | nil => rfl
  | cons h t ih =>
    simp [List.length, len_cons, ih]
    rw [Nat.add_comm]
