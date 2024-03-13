import Lean

open Lean
open Lean.Meta
def tst (declName : Name) : MetaM Unit := do
  IO.println (← getUnfoldEqnFor? declName)

mutual
def g (i j : Nat) : Nat :=
  if i < 5 then 0 else
  match j with
  | Nat.zero => 1
  | Nat.succ j => h i j
termination_by (i + j, 0)
decreasing_by
  simp_wf
  · apply Prod.Lex.left
    apply Nat.lt_succ_self

def h (i j : Nat) : Nat :=
  match j with
  | 0 => g i 0
  | Nat.succ j => g i j
termination_by (i + j, 1)
decreasing_by
  all_goals simp_wf
  · apply Prod.Lex.right
    decide
  · apply Prod.Lex.left
    apply Nat.lt_succ_self
end

#eval tst ``g
#check g.eq_1
#check g.eq_2
#check g.def
#eval tst ``h
#check h.eq_1
#check h.eq_2
#check h.def
