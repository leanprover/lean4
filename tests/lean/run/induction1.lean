@[recursor 4]
def Or.elim2 {p q r : Prop} (major : p ∨ q) (left : p → r) (right : q → r) : r :=
  match  major with
  | Or.inl h => left h
  | Or.inr h => right h

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
induction h
| inr h2 => exact Or.inl h2
| inl h1 => exact Or.inr h1

theorem tst2 {p q : Prop } (h : p ∨ q) : q ∨ p := by
induction h using elim2
| left _  => apply Or.inr; assumption
| right _ => apply Or.inl; assumption

theorem tst2b {p q : Prop } (h : p ∨ q) : q ∨ p := by
induction h using elim2
| left => apply Or.inr; assumption
| _ => apply Or.inl; assumption

theorem tst3 {p q : Prop } (h : p ∨ q) : q ∨ p := by
induction h using elim2
| right h => exact Or.inl h
| left h  => exact Or.inr h

theorem tst4 {p q : Prop } (h : p ∨ q) : q ∨ p := by
induction h using elim2
| right h => ?myright
| left h  => ?myleft
case myleft  => exact Or.inr h
case myright => exact Or.inl h

theorem tst5 {p q : Prop } (h : p ∨ q) : q ∨ p := by
induction h using elim2
| right h => _
| left h  =>
  refine Or.inr ?_
  exact h
case right => exact Or.inl h

theorem tst6 {p q : Prop } (h : p ∨ q) : q ∨ p :=
by {
  cases h
  | inr h2 => exact Or.inl h2
  | inl h1 => exact Or.inr h1
}

theorem tst7 {α : Type} (xs : List α) (h : (a : α) → (as : List α) → xs ≠ a :: as) : xs = [] :=
by {
  induction xs
  | nil          => exact rfl
  | cons z zs ih => exact absurd rfl (h z zs)
}

theorem tst8 {α : Type} (xs : List α) (h : (a : α) → (as : List α) → xs ≠ a :: as) : xs = [] := by {
  induction xs;
  exact rfl;
  exact absurd rfl $ h _ _
}

theorem tst9 {α : Type} (xs : List α) (h : (a : α) → (as : List α) → xs ≠ a :: as) : xs = [] := by
  cases xs
     | nil       => exact rfl
     | cons z zs => exact absurd rfl (h z zs)

theorem tst10 {p q : Prop } (h₁ : p ↔ q) (h₂ : p) : q := by
  induction h₁
  | intro h _ => exact h h₂

def Iff2 (m p q : Prop) := p ↔ q

theorem tst11 {p q r : Prop } (h₁ : Iff2 r p q) (h₂ : p) : q := by
  induction h₁ using Iff.rec
  | intro h _ => exact h h₂

theorem tst12 {p q : Prop } (h₁ : p ∨ q) (h₂ : p ↔ q) (h₃ : p) : q := by
  failIfSuccess induction h₁ using Iff.casesOn
  induction h₂ using Iff.casesOn
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
  cases x
  | leaf₁ => rfl
  | _     => injection h

theorem tst14 (x : Tree) (h : x = Tree.leaf₁) : x.isLeaf₁ = true := by
  induction x
  | leaf₁ => rfl
  | _     => injection h

inductive Vec (α : Type) : Nat → Type
  | nil  : Vec α 0
  | cons : (a : α) → {n : Nat} → (as : Vec α n) → Vec α (n+1)

def getHeads {α β} {n} (xs : Vec α (n+1)) (ys : Vec β (n+1)) : α × β := by
  cases xs
  cases ys
  apply Prod.mk
  assumption
  assumption
  done
