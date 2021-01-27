mutual

  inductive Arg (α : Type u) where
    | val  (a : α)
    | expr (e : Expr α)

  inductive Expr (α : Type u) where
    | app (f : String) (a : List (Arg α))

end

theorem aux_1 [SizeOf α] (a : List (Arg α)) : Arg._sizeOf_3 a = sizeOf a := by
  induction a with
  | nil => rfl
  | cons h t ih =>
    show 1 + Arg._sizeOf_1 h + Arg._sizeOf_3 t = sizeOf (h :: t)
    rw ih
    rfl
