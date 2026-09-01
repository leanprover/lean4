inductive Vector' (α : Type u) : Nat → Type u
  | nil : Vector' α 0
  | cons : α → Vector' α n → Vector' α (n+1)

infix:67 " :: " => Vector'.cons

inductive Ty where
  | int
  | bool
  | fn (a r : Ty)

abbrev Ty.interp : Ty → Type
  | int    => Int
  | bool   => Bool
  | fn a r => a.interp → r.interp

inductive HasType : Fin n → Vector' Ty n → Ty → Type where
  | stop : HasType 0 (ty :: ctx) ty
  | pop  : HasType k ctx ty → HasType k.succ (u :: ctx) ty

inductive Expr : Vector' Ty n → Ty → Type where
  | var   : HasType i ctx ty → Expr ctx ty
  | val   : Int → Expr ctx Ty.int
  | lam   : Expr (a :: ctx) ty → Expr ctx (Ty.fn a ty)
  | app   : Expr ctx (Ty.fn a ty) → Expr ctx a → Expr ctx ty
  | op    : (a.interp → b.interp → c.interp) → Expr ctx a → Expr ctx b → Expr ctx c
  | ife   : Expr ctx Ty.bool → Expr ctx a → Expr ctx a → Expr ctx a
  | delay : (Unit → Expr ctx a) → Expr ctx a

inductive Env : Vector' Ty n → Type where
  | nil  : Env Vector'.nil
  | cons : Ty.interp a → Env ctx → Env (a :: ctx)

infix:67 " :: " => Env.cons

def lookup : HasType i ctx ty → Env ctx → ty.interp
  | .stop,  x :: xs => x
  | .pop k, x :: xs => lookup k xs

def interp (env : Env ctx) : Expr ctx ty → ty.interp := fun e =>
  match e with
  | .var i     => lookup i env
  | .val x     => x
  | .lam b     => fun x => interp (x :: env) b
  | .app f a   => interp env f (interp env a)
  | .op o x y  => o (interp env x) (interp env y)
  | .ife c t e => if interp env c then interp env t else interp env e
  | .delay a   => interp env (a ())

open Expr

/- Examples -/

def add : Expr ctx (Ty.fn Ty.int (Ty.fn Ty.int Ty.int)) :=
  lam (lam (op (.+.) (var .stop) (var (.pop .stop))))

#guard interp Env.nil add 10 20 == 30

def fact : Expr ctx (Ty.fn Ty.int Ty.int) :=
  lam (ife (op (.==.) (var .stop) (val 0))
           (val 1)
           (op (.*.) (delay fun _ => app fact (op (.-.) (var .stop) (val 1))) (var .stop)))
  decreasing_by sorry

#guard interp Env.nil fact 10 == 3628800
