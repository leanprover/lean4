inductive Expr where
  | val : Nat → Expr
  | add : Expr → Expr → Expr
  | fn  : (Nat → Expr) → Expr

inductive Pos : Expr → Prop
  | base : (n : Nat) → Pos (Expr.val n.succ)
  | add  : Pos e₁ → Pos e₂ → Pos (Expr.add e₁ e₂)
  | fn   : ((n : Nat) → Pos (f n)) → Pos (Expr.fn f)

#print Pos.below
#print Pos.brecOn
