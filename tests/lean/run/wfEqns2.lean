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
def h (i j : Nat) : Nat :=
  match j with
  | 0 => g i 0
  | Nat.succ j => g i j
end
termination_by'
 invImage
    (fun
      | PSum.inl n => (n, 0)
      | PSum.inr n => (n, 1))
    (Prod.lex sizeOfWFRel sizeOfWFRel)
decreasing_by
  simp_wf
  first
  | apply Prod.Lex.left
    apply Nat.lt_succ_self
  | apply Prod.Lex.right
    decide

#eval tst ``g
#check g._eq_1
#check g._eq_2
#check g._unfold
#eval tst ``h
#check h._eq_1
#check h._eq_2
#check h._unfold
