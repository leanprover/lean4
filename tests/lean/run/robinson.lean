inductive Term
  | Var (i : Nat)
  | Cons (l : Term) (r : Term)

def Subst := Nat → Nat

def depth : Term → Nat
  | .Var _ => 0
  | .Cons l r => 1 + depth l + depth r

def act (f : Subst) (t : Term) := match t with
  | .Var i => Term.Var (f i)
  | .Cons l r => Term.Cons (act f l) (act f r)

def strangers (u v : Term) := ∀ f : Subst, act f u ≠ act f v

abbrev P (c : Option Subst) u v := match c with
  | none => strangers u v
  | some f => act f u = act f v

instance rel : WellFoundedRelation (Term × Term) := measure (λ (u, v) => depth u + depth v)

theorem decr_left (l₁ r₁ l₂ r₂ : Term) :
  rel.rel (l₁, l₂) (Term.Cons l₁ r₁, Term.Cons l₂ r₂) := by
  suffices h : depth l₁ + depth l₂ < depth (Term.Cons l₁ r₁) + depth (Term.Cons l₂ r₂) from h
  admit

theorem decr_right (l₁ r₁ l₂ r₂ : Term) (f : Subst) :
  rel.rel (act f r₁, act f r₂) (Term.Cons l₁ r₁, Term.Cons l₂ r₂) := by
  suffices h : depth (act f r₁) + depth (act f r₂) < depth (Term.Cons l₁ r₁) + depth (Term.Cons l₂ r₂) from h
  admit

def robinson (u v : Term) : { f : Option Subst // P f u v } := match u, v with
  | .Cons l₁ r₁, .Cons l₂ r₂ => match robinson l₁ l₂ with
    | ⟨ none, h ⟩ => ⟨ none, sorry ⟩
    | ⟨ some f, h ⟩ => match robinson (act f r₁) (act f r₂) with
      | ⟨ none, h ⟩ => ⟨ none, sorry ⟩
      | ⟨ some g, h ⟩ => ⟨ some (g ∘ f), sorry ⟩
  | .Var i, .Cons l r => ⟨ none, sorry ⟩
  | .Cons l r, .Var i => ⟨ none, sorry ⟩
  | .Var i, .Var j =>
    if i = j then ⟨ some id, sorry ⟩
    else ⟨ some λ n => if n = i then j else n, sorry ⟩
termination_by _ u v => (u, v)
decreasing_by
  first
    | apply decr_left _ _ _ _
    | apply decr_right _ _ _ _ _

attribute [simp] robinson

set_option pp.proofs true
#check robinson._eq_1
#check robinson._eq_2
#check robinson._eq_3
#check robinson._eq_4

theorem ex : (robinson (Term.Var 0) (Term.Var 0)).1 = some id := by
  unfold robinson
  admit
