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
#check g._eq_1
#check g._eq_2
#check g._unfold
#eval tst ``h
#check h._eq_1
#check h._eq_2
#check h._unfold
