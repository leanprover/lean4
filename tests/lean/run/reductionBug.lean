abbrev VName := String

inductive Ty where
  | Bool
  | Int

def Ctxt := VName → Option Ty

variable (Γ : Ctxt) in
inductive Expr : Ty → Type where
  | var (h : Γ x = some τ) : Expr τ

def Expr.constFold : Expr Γ τ → Option Unit
  | var n   => none

theorem Expr.constFold_sound {e : Expr Γ τ} : constFold e = some v → True := by
  intro h
  induction e with
  | var   => simp only [reduceCtorEq, constFold] at h
