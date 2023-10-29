import Lean

open Lean
open Lean.Meta
def tst (declName : Name) : MetaM Unit := do
  IO.println (← getUnfoldEqnFor? declName)

mutual
  def f : Nat → α → α → α
    | 0, a, b => a
    | n, a, b => g a n b |>.1

  def g : α → Nat → α → (α × α)
    | a, 0, b => (a, b)
    | a, n, b => (h a b n, a)

  def h : α → α → Nat → α
    | a, b, 0 => b
    | a, b, n+1 => f n a b
end
termination_by'
  invImage
    (fun
      | PSum.inl ⟨n, _, _⟩ => (n, 2)
      | PSum.inr <| PSum.inl ⟨_, n, _⟩ => (n, 1)
      | PSum.inr <| PSum.inr ⟨_, _, n⟩ => (n, 0))
    (Prod.lex sizeOfWFRel sizeOfWFRel)
decreasing_by
  simp_wf
  first
  | apply Prod.Lex.left
    apply Nat.lt_succ_self
  | apply Prod.Lex.right
    decide

#eval f 5 'a' 'b'

#eval tst ``f
#check @f._eq_1
#check @f._eq_2
#check @f._unfold


#eval tst ``h
#check @h._eq_1
#check @h._eq_2
#check @h._unfold
