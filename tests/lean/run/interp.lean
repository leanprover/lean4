inductive Vector (α : Type u) : Nat → Type u
  | nil : Vector α 0
  | cons : α → Vector α n → Vector α (n+1)

infix:67 (priority := high) " :: " => Vector.cons

inductive Index : Nat → Type
  | zero : Index (n+1)
  | succ : Index n → Index (n+1)

instance : OfNat (Index (n+1)) (nat_lit 0) where
  ofNat := Index.zero

inductive Ty where
  | int
  | bool
  | fn (a ty : Ty)

@[reducible] def Ty.interp : Ty → Type
  | int    => Int
  | bool   => Bool
  | fn a b => a.interp → b.interp

inductive HasType : Index n → Vector Ty n → Ty → Type where
  | stop {ctx : Vector Ty n} : HasType 0 (ty :: ctx) ty
  | pop  {ctx : Vector Ty n} : HasType k ctx ty → HasType k.succ (u :: ctx) ty

open HasType (stop pop)

inductive Expr : Vector Ty n → Ty → Type where
  | var {ctx : Vector Ty n} : HasType i ctx ty → Expr ctx ty
  | val {ctx : Vector Ty n} : Int → Expr ctx Ty.int
  | lam {ctx : Vector Ty n} : Expr (a :: ctx) ty → Expr ctx (Ty.fn a ty)
  | app {ctx : Vector Ty n} : Expr ctx (Ty.fn a ty) → Expr ctx a → Expr ctx ty
  | op  {ctx : Vector Ty n} : (a.interp → b.interp → c.interp) → Expr ctx a → Expr ctx b → Expr ctx c
  | ife {ctx : Vector Ty n} : Expr ctx Ty.bool → (Unit → Expr ctx a) → (Unit → Expr ctx a) → Expr ctx a

inductive Env : Vector Ty n → Type where
  | nil  : Env Vector.nil
  | cons {ctx : Vector Ty n} : Ty.interp a → Env ctx → Env (a :: ctx)

def Env.lookup : {ctx : Vector Ty n} → HasType i ctx ty → Env ctx → ty.interp
  | _, stop,  Env.cons x xs => x
  | _, pop k, Env.cons x xs => lookup k xs

def Expr.interp {ctx : Vector Ty n} (env : Env ctx) : Expr ctx ty → ty.interp
  | var i     => env.lookup i
  | val x     => x
  | lam b     => fun x => b.interp (Env.cons x env)
  | app f a   => f.interp env (a.interp env)
  | op o x y  => o (x.interp env) (y.interp env)
  | ife c t e => if c.interp env then t () |>.interp env else e () |>.interp env

open Expr

/- Examples -/

def add {ctx : Vector Ty n} : Expr ctx (Ty.fn Ty.int (Ty.fn Ty.int Ty.int)) :=
  lam (lam (op (.+.) (var stop) (var (pop stop))))

#eval add.interp Env.nil 10 20

def fact {ctx : Vector Ty n} : Expr ctx (Ty.fn Ty.int Ty.int) :=
  lam (ife (op (.==.) (var stop) (val 0))
           (fun _ => val 1)
           (fun _ => op (.*.) (app fact (op (.-.) (var stop) (val 1))) (var stop)))
  decreasing_by sorry

#eval fact.interp Env.nil 10
