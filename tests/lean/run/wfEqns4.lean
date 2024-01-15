import Lean

open Lean
open Lean.Meta
def tst (declName : Name) : MetaM Unit := do
  IO.println (← getUnfoldEqnFor? declName)

mutual
  def f : Nat → α → α → α
    | 0, a, b => a
    | n, a, b => g a n b |>.1
  termination_by n _ _ => (n, 2)
  decreasing_by
    simp_wf
    apply Prod.Lex.right
    decide

  def g : α → Nat → α → (α × α)
    | a, 0, b => (a, b)
    | a, n, b => (h a b n, a)
  termination_by _ n _ => (n, 1)
  decreasing_by
    simp_wf
    apply Prod.Lex.right
    decide

  def h : α → α → Nat → α
    | a, b, 0 => b
    | a, b, n+1 => f n a b
  termination_by _ _ n => (n, 0)
  decreasing_by
    simp_wf
    apply Prod.Lex.left
    apply Nat.lt_succ_self
end

#eval f 5 'a' 'b'

#eval tst ``f
#check @f._eq_1
#check @f._eq_2
#check @f._unfold


#eval tst ``h
#check @h._eq_1
#check @h._eq_2
#check @h._unfold
