new_frontend

theorem tst1 {α : Type} {p : Prop} (xs : List α) (h₁ : (a : α) → (as : List α) → xs = a :: as → p) (h₂ : xs = [] → p) : p :=
by match h:xs with
   | []    => exact h₂ h
   | z::zs => apply h₁ z zs; assumption

theorem tst2 {α : Type} {p : Prop} (xs : List α) (h₁ : (a : α) → (as : List α) → xs = a :: as → p) (h₂ : xs = [] → p) : p :=
by match h:xs with
   | []    => ?nilCase
   | z::zs => ?consCase;
   case consCase => exact h₁ z zs h;
   case nilCase => exact h₂ h

def tst3 {α β γ : Type} (h : α × β × γ) : β × α × γ :=
by {
  match h with
  | (a, b, c) => exact (b, a, c)
}

theorem tst4 {α : Type} {p : Prop} (xs : List α) (h₁ : (a : α) → (as : List α) → xs = a :: as → p) (h₂ : xs = [] → p) : p :=
by {
  match h:xs with
  | []    => _
  | z::zs => _;
  case match_2 => exact h₁ z zs h;
  exact h₂ h
}

theorem tst5 {p q r} (h : p ∨ q ∨ r) : r ∨ q ∨ p:=
by {
  match h with
  | Or.inl h          => exact Or.inr (Or.inr h)
  | Or.inr (Or.inl h) => ?c1
  | Or.inr (Or.inr h) => ?c2;
  case c2 => apply Or.inl; assumption;
  case c1 => apply Or.inr; apply Or.inl; assumption
}

theorem tst6 {p q r} (h : p ∨ q ∨ r) : r ∨ q ∨ p:=
by {
  match h with
  | Or.inl h          => exact Or.inr (Or.inr h)
  | Or.inr (Or.inl h) => ?c1
  | Or.inr (Or.inr h) =>
    apply Or.inl;
    assumption;
  case c1 => apply Or.inr; apply Or.inl; assumption
}

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
