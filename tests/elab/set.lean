def Set (α : Type u) := α → Prop
def Set.in (s : Set α) (a : α) := s a

notation:50 a " ∈ " s:50 => Set.in s a

def Set.pred (p : α → Prop) : Set α := p

notation "{" a "|" p "}" => Set.pred (fun a => p)

theorem ex1 : (1, 3) ∈ { (n, m) | n < 2 ∧ m < 5 } := by
  simp (config := { decide := true }) [Set.in, Set.pred]

def Set.union (s₁ s₂ : Set α) : Set α :=
  { a | a ∈ s₁ ∨ a ∈ s₂ }

infix:65 " ∪ " => Set.union

def Set.inter (s₁ s₂ : Set α) : Set α :=
  { a | a ∈ s₁ ∧ a ∈ s₂ }

infix:70 " ∩ " => Set.inter

instance (s : Set α) [h : Decidable (s a)] : Decidable (a ∈ Set.pred s) :=
  h

instance (s₁ s₂ : Set α) [Decidable (a ∈ s₁)] [Decidable (a ∈ s₂)] : Decidable (a ∈ s₁ ∩ s₂) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (s₁ s₂ : Set α) [Decidable (a ∈ s₁)] [Decidable (a ∈ s₂)] : Decidable (a ∈ s₁ ∪ s₂) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem ex2 : (1, 3) ∈ { (x, y) | x < y } :=
  by decide

theorem ex3 : (10000, 300000) ∈ { (x, y) | x < y } ∩ { (x, y) | x = 10000 } :=
  by decide
