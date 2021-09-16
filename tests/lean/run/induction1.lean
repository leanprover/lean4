theorem tst0 {p q : Prop } (h : p ∨ q) : q ∨ p :=
by {
  induction h;
  { apply Or.inr; assumption };
  { apply Or.inl; assumption }
}

theorem tst0' {p q : Prop } (h : p ∨ q) : q ∨ p := by
induction h
focus
  apply Or.inr
  assumption
focus
  apply Or.inl
  assumption

theorem tst1 {p q : Prop } (h : p ∨ q) : q ∨ p := by
induction h with
| inr h2 => exact Or.inl h2
| inl h1 => exact Or.inr h1

theorem tst6 {p q : Prop } (h : p ∨ q) : q ∨ p :=
by {
  cases h with
  | inr h2 => exact Or.inl h2
  | inl h1 => exact Or.inr h1
}

theorem tst7 {α : Type} (xs : List α) (h : (a : α) → (as : List α) → xs ≠ a :: as) : xs = [] :=
by {
  induction xs with
  | nil          => exact rfl
  | cons z zs ih => exact absurd rfl (h z zs)
}

theorem tst8 {α : Type} (xs : List α) (h : (a : α) → (as : List α) → xs ≠ a :: as) : xs = [] := by {
  induction xs;
  exact rfl;
  exact absurd rfl $ h _ _
}

theorem tst9 {α : Type} (xs : List α) (h : (a : α) → (as : List α) → xs ≠ a :: as) : xs = [] := by
  cases xs with
     | nil       => exact rfl
     | cons z zs => exact absurd rfl (h z zs)

theorem tst10 {p q : Prop } (h₁ : p ↔ q) (h₂ : p) : q := by
  induction h₁ with
  | intro h _ => exact h h₂

def Iff2 (m p q : Prop) := p ↔ q

theorem tst11 {p q r : Prop } (h₁ : Iff2 r p q) (h₂ : p) : q := by
  induction h₁ using Iff.rec with
  | intro h _ => exact h h₂

theorem tst12 {p q : Prop } (h₁ : p ∨ q) (h₂ : p ↔ q) (h₃ : p) : q := by
  fail_if_success induction h₁ using Iff.casesOn
  induction h₂ using Iff.casesOn with
  | intro h _ =>
    exact h h₃

inductive Tree
  | leaf₁
  | leaf₂
  | node : Tree → Tree → Tree

def Tree.isLeaf₁ : Tree → Bool
  | leaf₁ => true
  | _     => false

theorem tst13 (x : Tree) (h : x = Tree.leaf₁) : x.isLeaf₁ = true := by
  cases x with
  | leaf₁ => rfl
  | _     => injection h

theorem tst14 (x : Tree) (h : x = Tree.leaf₁) : x.isLeaf₁ = true := by
  induction x with
  | leaf₁ => rfl
  | _     => injection h

inductive Vec (α : Type) : Nat → Type
  | nil  : Vec α 0
  | cons : (a : α) → {n : Nat} → (as : Vec α n) → Vec α (n+1)

def getHeads {α β} {n} (xs : Vec α (n+1)) (ys : Vec β (n+1)) : α × β := by
  cases xs
  cases ys
  apply Prod.mk
  repeat
    trace_state
    assumption
  done

theorem ex1 (n m o : Nat) : n = m + 0 → m = o → m = o := by
  intro (h₁ : n = m) h₂
  rw [← h₁, ← h₂]
  assumption
