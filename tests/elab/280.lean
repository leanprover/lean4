inductive S where
  | P
  | I

open S

inductive Expr : S → Type where
  | lit : Int → Expr I
  | eq : Expr I → Expr I → Expr P

def Val : S → Type
  | P => Prop
  | I => Int

def eval : {s : S} → Expr s → Val s
  | _, (Expr.lit n) => n
  | _, (Expr.eq e₁ e₂) => eval e₁ = eval e₂

def eval' : Expr s → Val s
  | Expr.lit n    => n
  | Expr.eq e₁ e₂ => eval e₁ = eval e₂
