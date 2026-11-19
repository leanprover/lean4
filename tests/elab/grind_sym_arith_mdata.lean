/-!
The `Sym.Arith` normalizer must not panic on metadata inside an arithmetic term. The conditions
of `match` equations keep the `_inaccessible` annotation on pattern terms, e.g.
`a = [mdata _inaccessible] n + 1 + 1`; `match_expr` sees through the annotation, so the
structural destructuring that followed it panicked (`unreachable code`, `Expr.appFn!`).
-/
set_option backward.grind.normalizer false

inductive Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n+1)

def h (v w : Vec α n) : Nat :=
  match v, w with
  | _, .cons _ (.cons _ _) => 20
  | .nil, _ => 30
  | _, _    => 40

example (a b : Vec α n) : h a b > 0 := by
  grind [h.eq_def]

example (a : Vec α (n + 1 + 1)) (x y : α) (c : Vec α n) : h a (.cons x (.cons y c)) = 20 := by
  grind [h.eq_def]
