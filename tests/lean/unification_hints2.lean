open nat

constant F : nat → Type
constant F.suc (n : nat) (f : F n) : F (succ n)
constant F.raise (n m : nat) (f : F m) : F (m + n)

example (m n : nat) (i : F m) : F.raise (succ n) m i = F.suc _ (F.raise n _ i) :=
begin
  trace_state, -- the result should not contain recursor applications because the stdlib contains the unification hint add_succ_defeq_succ_add_hint
  admit
end


@[unify] def {u} cons_append_hint (α : Type u) (a b : α) (l₁ l₂ l₃: list α) : unification_hint :=
{ pattern     := (a :: l₁) ++ l₂ =?= b :: l₃,
  constraints := [l₃ =?= l₁ ++ l₂, a =?= b] }

constant {u} G (α : Type u) : list α → Type
constant {u} G.cons (α : Type u) (a : α) (l : list α) (g : G α l) : G α (a :: l)
constant {u} G.raise (α : Type u) (l₁ l₂ : list α) (g : G α l₂) : G α (l₁ ++ l₂)

universe u

example (α : Type u) (a b : α) (l₁ l₂ : list α) (i : G α l₂) : G.raise α (a::l₁) l₂ i = G.cons α a _ (G.raise α _ _ i) :=
begin
  trace_state, -- the result should not contain recursor applications because we declared cons_append_hint above
  admit
end
