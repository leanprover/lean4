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

theorem Arg.val.sizeOf_spec [SizeOf α] (a : α) : sizeOf (Arg.val a) = 1 + sizeOf a :=
  rfl

theorem Arg.expr.sizeOf_spec [SizeOf α] (e : Expr α) : sizeOf (Arg.expr e) = 1 + sizeOf e :=
  rfl

theorem Expr.app.sizeOf_spec [SizeOf α] (f : String) (args : List (Arg α)) : sizeOf (Expr.app f args) = 1 + sizeOf f + sizeOf args := by
  show 1 + sizeOf f + Arg._sizeOf_3 args = 1 + sizeOf f + sizeOf args
  rw aux_1
