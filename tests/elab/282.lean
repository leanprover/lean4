open Classical

inductive S where
  | B
  | I

open S

inductive Expr : S → Type where
  | lit : Int → Expr I
  | eq {s : S} : Expr s → Expr s → Expr B

def Val : S → Type
  | B => Bool
  | I => Int

noncomputable def Expr.eval : {s : S} → Expr s → Val s
  | _, lit n => n
  | _, eq e₁ e₂ => decide (e₁.eval = e₂.eval)
