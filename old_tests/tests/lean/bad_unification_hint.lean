-- Good hint
@[unify] def {u} cons_append_hint (α : Type u) (a b : α) (l₁ l₂ l₃: list α) : unification_hint :=
{ pattern     := (a :: l₁) ++ l₂ =?= b :: l₃,
  constraints := [l₃ =?= l₁ ++ l₂, a =?= b] }

-- Bad hint: pattern is incorrect
@[unify] def {u} append_cons_hint (α : Type u) (a b : α) (l₁ l₂ l₃: list α) : unification_hint :=
{ pattern     := l₁ ++ (a :: l₂) =?= b :: l₃,
  constraints := [l₃ =?= l₁ ++ l₂, a =?= b] }

-- Bad hint: constraint #1 is incorrect
@[unify] def {u} cons_append_hint' (α : Type u) (a b : α) (l₁ l₂ l₃: list α) : unification_hint :=
{ pattern     := (a :: l₁) ++ l₂ =?= b :: l₃,
  constraints := [l₃ =?= l₁ ++ l₃, a =?= b] }
