-- From @joehendrix
-- The imul doesn't type check as Lean won't try to coerce from a reg (bv 64) to a expr (bv ?u)


inductive MCType
| bv : Nat → MCType

open MCType

inductive Reg : MCType → Type
| rax (n : Nat) : Reg (bv n)

inductive Expr : MCType → Type
| r : ∀{tp:MCType}, Reg tp → Expr tp
| sextC {s:Nat} (x : Expr (bv s)) (t:Nat) : Expr (bv t)

instance reg_is_expr {tp:MCType} : Coe (Reg tp) (Expr tp) := ⟨Expr.r⟩

def bvmul {w:Nat} (x y : Expr (bv w)) : Expr (bv w) := x

/-
Remark: Joe's original example used the following definition.
```
def sext {s:Nat} (x : Expr (bv s)) (t:Nat) : Expr (bv t) := Expr.sextC x t
```
This definition is bad because the parameter `s` is unconstrained.
Type class resolution gets stuck at
```
CoeT (Reg (bv 64)) (Reg.rax 64) (Expr (bv ?m_1))
```
It would have to set `?m_1 := 64` which is not allowed since TC should
not change external TC metavariables.
I fixed the problem by changing the definition. Now,
type inference will enforce that `?m_1` must be 64, and TC will be able
to synthesize the instance.
-/
def sext {s:Nat} (x : Expr (bv s)) (n:Nat) : Expr (bv (s+n)) := Expr.sextC x (s+n)

open MCType

variable {u:Nat} (e : Expr (bv 64))
#check (bvmul (sext (Reg.rax 64) 64) (sext e 64) : Expr (bv 128))
