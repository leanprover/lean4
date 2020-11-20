-- Renaming for intrinsically typed lambda calculus

inductive Ty
  | base
  | arr (a b : Ty)

def Cxt := List Ty

inductive Var : (g : Cxt) → (a : Ty) → Type
  | vz {g a}   : Var (a :: g) a
  | vs {g a b} : Var g a → Var (b :: g) a

inductive Term : Cxt → Ty → Type
  | var {g a}   : Var g a → Term g a
  | app {g a b} : Term g (Ty.arr a b) → Term g a → Term g b
  | abs {g a b} : Term (a :: g) b → Term g (Ty.arr a b)

def Ren (g d : Cxt) :=
  (a : Ty) → Var d a → Var g a

def liftr {g d a} (r : Ren g d) : Ren (a :: g) (a :: d)
  | _, Var.vz   => Var.vz
  | _, Var.vs x => Var.vs (r _ x)

def rename {g d : Cxt} : (r : Ren g d) → {a : Ty} → Term d a → Term g a
  | r, _, Term.var x   => Term.var (r _ x)
  | r, _, Term.app t u => Term.app (rename r t) (rename r u)
  | r, _, Term.abs t   => Term.abs (rename (liftr r) t)
