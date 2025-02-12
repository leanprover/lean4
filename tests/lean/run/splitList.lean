inductive ListSplit : List α → Type _
  | split l₁ l₂ : ListSplit (l₁ ++ l₂)

def splitList : (l : List α) → ListSplit l
  | [] => ListSplit.split [] []
  | h :: t => ListSplit.split [h] t

@[simp] def ListSplit.left {as : List α} : ListSplit as → List α
  | split a b => a

@[simp] def ListSplit.right {as : List α} : ListSplit as → List α
  | split a b => b

/-- Helper theorem for justifying termination. -/
theorem splitList_length (as : List α) (h₁ : as.length > 1) (h₂ : as = bs) : (splitList as).left.length < bs.length ∧ (splitList as).right.length < bs.length := by
  match as with
  | [] => contradiction
  | a :: as => simp +arith [← h₂, splitList]; simp +arith at h₁; assumption

def len : List α → Nat
  | []      => 0
  | a :: [] => 1
  | l@h₁:(a :: b :: as) =>
    -- Remark: we didn't use `_` because we currently don't have a way for getting a hypothesis stating that the previous two case were not taken here.
    -- h₁ : l = a :: b :: as
    match h₂ : splitList l with
    | ListSplit.split fst snd =>
      -- Remark: `match` refined `h₁`s type to `h₁ : fst ++ snd = a :: b :: as`
      -- h₂ : HEq (splitList l) (ListSplit.split fst snd)
      have := splitList_length (fst ++ snd) (by simp +arith [h₁]) h₁
      -- The following two proofs ase used to justify the recursive applications `len fst` and `len snd`
      have dec₁ : fst.length < as.length + 2 := by subst l; simp +arith [eq_of_heq h₂] at this |- ; simp [this]
      have dec₂ : snd.length < as.length + 2 := by subst l; simp +arith [eq_of_heq h₂] at this |- ; simp [this]
      len fst + len snd
termination_by xs => xs.length


-- The equational theorems are
#check @len.eq_1
#check @len.eq_2
#check @len.eq_3
#check @len.eq_def

theorem len_nil : len ([] : List α) = 0 := by
  simp [len]

theorem len_1 (a : α) : len [a] = 1 := by
  simp [len]

theorem len_2 (a b : α) (bs : List α) : len (a::b::bs) = 1 + len (b::bs) := by
  simp [len, splitList]

theorem len_cons (a : α) (as : List α) : len (a::as) = 1 + len as := by
  cases as with
  | nil => simp [len_1, len_nil]
  | cons b bs => simp [len_2]

theorem listlen : ∀ l : List α, l.length = len l := by
  intro l
  induction l with
  | nil => simp [len_nil]
  | cons h t ih =>
    simp [List.length, len_cons, ih]
    rw [Nat.add_comm]

namespace Ex2

/--
`len` example again but with the proofs at `decreasing_by`
-/
def len : List α → Nat
  | []      => 0
  | a :: [] => 1
  | l@h₁:(a :: b :: as) =>
    match h₂ : l, h₃ : splitList l with
    | _, ListSplit.split fst snd =>
      len fst + len snd
termination_by xs => xs.length
decreasing_by
  all_goals
    have := splitList_length (fst ++ snd) (by simp +arith [h₁]) h₁
    subst h₂
    simp +arith [eq_of_heq h₃] at this |- ; simp [this]

-- The equational theorems are
#check @len.eq_1
#check @len.eq_2
#check @len.eq_3
#check @len.eq_def

theorem len_nil : len ([] : List α) = 0 := by
  simp [len]

theorem len_1 (a : α) : len [a] = 1 := by
  simp [len]

theorem len_2 (a b : α) (bs : List α) : len (a::b::bs) = 1 + len (b::bs) := by
  conv => lhs; unfold len
  simp [len, splitList]

theorem len_cons (a : α) (as : List α) : len (a::as) = 1 + len as := by
  cases as with
  | nil => simp [len_1, len_nil]
  | cons b bs => simp [len_2]

theorem listlen : ∀ l : List α, l.length = len l := by
  intro l
  induction l with
  | nil => simp [len_nil]
  | cons h t ih =>
    simp [List.length, len_cons, ih]
    rw [Nat.add_comm]

end Ex2
