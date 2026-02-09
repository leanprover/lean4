variable (R : α → α → Prop)

inductive List.Pairwise' : List α → Prop
  | nil : Pairwise' []
  | cons : ∀ {a : α} {l : List α}, (∀ {a} (_ : a' ∈ l), R a a') → Pairwise' l → Pairwise' (a :: l)

theorem pairwise_append {l₁ l₂ : List α} :
    (l₁ ++ l₂).Pairwise' R ↔ l₁.Pairwise' R ∧ l₂.Pairwise' R ∧ ∀ {a} (_ : a ∈ l₁), ∀ {b} (_ : b ∈ l₂), R a b := by
  induction l₁ <;> simp [*, and_left_comm]
  repeat sorry
