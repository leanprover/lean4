-- From @joehendrix
-- The imul doesn't type check as Lean won't try to coerce from a reg (bv 64) to a expr (bv ?u)

inductive MCType
| bv : Nat → MCType

open MCType

inductive Reg : MCType → Type
| rax : Reg (bv 64)

inductive Expr : MCType → Type
| r : ∀{tp:MCType}, Reg tp → Expr tp
| sextC {s:Nat} (x : Expr (bv s)) (t:Nat) : Expr (bv t)

instance reg_is_expr {tp:MCType} : HasCoe (Reg tp) (Expr tp) := ⟨Expr.r⟩

def bvmul {w:Nat} (x y : Expr (bv w)) : Expr (bv w) := x

def sext {s:Nat} (x : Expr (bv s)) (t:Nat) : Expr (bv t) := Expr.sextC x t

def imul {u:Nat} (e:Expr (bv 64)) : Expr (bv 128) :=
  bvmul (sext Reg.rax 128) (sext e _)
