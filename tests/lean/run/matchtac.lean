theorem tst1 {α : Type} {p : Prop} (xs : List α) (h₁ : (a : α) → (as : List α) → xs = a :: as → p) (h₂ : xs = [] → p) : p :=
by match (generalizing := false) h:xs with
   | []    => exact h₂ h
   | z::zs => apply h₁ z zs; assumption

theorem tst1' {α : Type} {p : Prop} (xs : List α) (h₁ : (a : α) → (as : List α) → xs = a :: as → p) (h₂ : xs = [] → p) : p :=
by match xs with
   | []    => exact h₂ rfl
   | z::zs => exact h₁ z zs rfl

theorem tst2 {α : Type} {p : Prop} (xs : List α) (h₁ : (a : α) → (as : List α) → xs = a :: as → p) (h₂ : xs = [] → p) : p :=
by match (generalizing := false) h:xs with
   | []    => ?nilCase
   | z::zs => ?consCase;
   case consCase => exact h₁ z zs h;
   case nilCase => exact h₂ h

def tst3 {α β γ : Type} (h : α × β × γ) : β × α × γ :=
by {
  match h with
  | (a, b, c) => exact (b, a, c)
}

theorem tst4 {α : Type} {p : Prop} (xs : List α) (h₁ : (a : α) → (as : List α) → xs = a :: as → p) (h₂ : xs = [] → p) : p := by
match (generalizing := false) h:xs with
| []    => _
| z::zs => _
case match_2 => exact h₁ z zs h
exact h₂ h

theorem tst5 {p q r} (h : p ∨ q ∨ r) : r ∨ q ∨ p:= by
match h with
| Or.inl h          => exact Or.inr (Or.inr h)
| Or.inr (Or.inl h) => ?c1
| Or.inr (Or.inr h) => ?c2
case c2 =>
  apply Or.inl
  assumption
case c1 =>
  apply Or.inr
  apply Or.inl
  assumption

theorem tst6 {p q r} (h : p ∨ q ∨ r) : r ∨ q ∨ p:= by
match h with
| Or.inl h          => exact Or.inr (Or.inr h)
| Or.inr (Or.inl h) => ?c1
| Or.inr (Or.inr h) =>
  apply Or.inl
  assumption
case c1 => apply Or.inr; apply Or.inl; assumption

theorem tst7 {p q r} (h : p ∨ q ∨ r) : r ∨ q ∨ p:=
by match h with
   | Or.inl h =>
     exact Or.inr (Or.inr h)
   | Or.inr (Or.inl h) =>
     apply Or.inr;
     apply Or.inl;
     assumption
   | Or.inr (Or.inr h) =>
     apply Or.inl;
     assumption

inductive ListLast.{u} {α : Type u} : List α → Type u
| empty    : ListLast []
| nonEmpty : (as : List α) → (a : α) → ListLast (as ++ [a])

axiom last {α} (xs : List α) : ListLast xs
axiom back {α} [Inhabited α] (xs : List α) : α
axiom popBack {α} : List α → List α
axiom backEq {α} [Inhabited α] : (xs : List α) → (x : α) → back (xs ++ [x]) = x
axiom popBackEq {α} : (xs : List α) → (x : α) → popBack (xs ++ [x]) = xs

theorem tst8 {α} [Inhabited α] (xs : List α) : xs ≠ [] → xs = popBack xs ++ [back xs] :=
match (generalizing := false) xs, h:last xs with
| _, ListLast.empty         => fun h => absurd rfl h
| _, ListLast.nonEmpty ys y => fun _ => sorry

theorem tst9 {α} [Inhabited α] (xs : List α) : xs ≠ [] → xs = popBack xs ++ [back xs] := by
  match (generalizing := false) xs, h:last xs with
  | _, ListLast.empty         => intro h; exact absurd rfl h
  | _, ListLast.nonEmpty ys y => intro; rw [popBackEq, backEq]

theorem tst8' {α} [Inhabited α] (xs : List α) : xs ≠ [] → xs = popBack xs ++ [back xs] :=
match xs, last xs with
| _, ListLast.empty         => fun h => absurd rfl h
| _, ListLast.nonEmpty ys y => fun _ => sorry

theorem tst8'' {α} [Inhabited α] (xs : List α) (h : xs ≠ []) : xs = popBack xs ++ [back xs] :=
match xs, last xs with
| _, ListLast.empty         => absurd rfl h
| _, ListLast.nonEmpty ys y => sorry
