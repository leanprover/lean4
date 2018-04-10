universe variables u
variable {α : Type u}

def app : list α → list α → list α
| []     l := l
| (h::t) l := h :: app t l

/- Mark the app equational lemmas as ematching rules -/
attribute [ematch] app

@[ematch] lemma app_nil_right (l : list α) : app l [] = l :=
begin [smt]
  induction l,
  ematch,
end

@[ematch] lemma app_assoc (l₁ l₂ l₃ : list α) : app (app l₁ l₂) l₃ = app l₁ (app l₂ l₃) :=
begin [smt]
  induction l₁,
  ematch,
  ematch
end

def len : list α → nat
| []       := 0
| (a :: l) := len l + 1

attribute [ematch] len add_zero zero_add

@[simp] lemma len_app (l₁ l₂ : list α) : len (app l₁ l₂) = len l₁ + len l₂ :=
begin [smt]
  induction l₁,
  {ematch, ematch},
  {ematch, ematch}
end
