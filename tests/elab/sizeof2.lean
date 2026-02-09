mutual

  inductive Arg (α : Type u) where
    | val  (a : α)
    | expr (e : Expr α)

  inductive Expr (α : Type u) where
    | app (f : String) (a : List (Arg α))

end

#print Expr.app.sizeOf_spec
