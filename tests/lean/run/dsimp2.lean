@[reducible, simp]
def eval {β : α → Sort _} (x : α) (f : ∀ x, β x) : β x := f x

-- For this to work, the above `simp` has to add `eval` also to the decls-to-unfold,
-- as the `eval.eq_1` is not helpful, as `eval` is reducible
theorem test [LE β] (x : α) (f : α → β) (P : β → Prop) (h : P (f x)) : P (eval x f) := by
  dsimp
  apply h
