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

/--
trace: case cons.cons.fst
α β : Type
n : Nat
a✝¹ : α
as✝¹ : Vec α n
a✝ : β
as✝ : Vec β n
⊢ α

case cons.cons.snd
α β : Type
n : Nat
a✝¹ : α
as✝¹ : Vec α n
a✝ : β
as✝ : Vec β n
⊢ β
case cons.cons.snd
α β : Type
n : Nat
a✝¹ : α
as✝¹ : Vec α n
a✝ : β
as✝ : Vec β n
⊢ β
-/
#guard_msgs in
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

/-!
Test of named generalization, of an expression that does not appear in the goal.
-/
/--
trace: case succ
α : Type
ys zs : List α
n : Nat
ih : ∀ (xs : List α), (xs ++ ys ++ zs).length = n → xs ++ ys ++ zs = xs ++ (ys ++ zs)
xs : List α
h : (xs ++ ys ++ zs).length = n + 1
⊢ xs ++ ys ++ zs = xs ++ (ys ++ zs)
-/
#guard_msgs in
example {α : Type} (xs ys zs : List α) : (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  induction h : ((xs ++ ys) ++ zs).length generalizing xs with
  | zero =>
    simp only [List.length_append, Nat.add_eq_zero_iff, List.length_eq_zero_iff] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    rfl
  | succ n ih =>
    trace_state
    cases xs with
    | nil => rfl
    | cons x xs' =>
      simp only [List.cons_append, List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.cons_append, ih _ h]

/-!
Test of named generalization, of an expression that appears in the goal.
-/
/--
trace: case cons
α : Type
zs : List α
w : α
ws : List α
ih : ∀ (xs ys : List α), xs ++ ys ++ zs = ws → ws = xs ++ (ys ++ zs)
xs ys : List α
h : xs ++ ys ++ zs = w :: ws
⊢ w :: ws = xs ++ (ys ++ zs)
-/
#guard_msgs in
example {α : Type} (xs ys zs : List α) : (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  induction h : (xs ++ ys) ++ zs generalizing xs ys with
  | nil =>
    cases xs <;> cases ys <;> cases zs <;> cases h
    rfl
  | cons w ws ih =>
    trace_state
    cases xs with
    | nil =>
      cases ys with
      | nil =>
        cases h
        rfl
      | cons _ ys' =>
        cases h
        rw [ih [] ys' rfl]
        rfl
    | cons _ xs' =>
      cases h
      rw [ih xs' ys rfl]
      rfl

/-!
Test of hole for named generalization.
Yields a fresh hygienic name.
-/
/--
trace: case zero
n : Nat
h✝ : n + 1 = 0
⊢ 0 = 1 + n

case succ
n n✝ : Nat
a✝ : n + 1 = n✝ → n✝ = 1 + n
h✝ : n + 1 = n✝ + 1
⊢ n✝ + 1 = 1 + n
-/
#guard_msgs in
example (n : Nat) : n + 1 = 1 + n := by
  induction _ : n + 1
  trace_state
  omega
  omega

/-!
Having no `=>` clause is short for `=> ?_`.
-/
/--
trace: case mk
p1 p2 : Nat
⊢ (p1, p2).fst = (p1, p2).fst
-/
#guard_msgs in
example (p : Nat × Nat) : p.1 = p.1 := by
  cases p with | _ p1 p2
  trace_state
  rfl

/-!
Can have multiple trailing `=>`-free goals. This is short for
```
induction n with | zero | succ n ih => ?_
```
which is short for
```
induction n with | zero => ?_ | succ n ih => ?_
```
-/
/--
trace: case zero
⊢ 0 + 1 = 1 + 0

case succ
n : Nat
ih : n + 1 = 1 + n
⊢ n + 1 + 1 = 1 + (n + 1)
-/
#guard_msgs in
example (n : Nat) : n + 1 = 1 + n := by
  induction n with | zero | succ n ih
  trace_state
  rfl
  omega
