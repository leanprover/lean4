import Lean

open Lean
open Lean.Meta
def tst (declName : Name) : MetaM Unit := do
  IO.println (← getUnfoldEqnFor? declName)

inductive Wk: Nat -> Nat -> Type 0 where
  | id: Wk n n
  | step: Wk m n -> Wk (Nat.succ m) n

def wk_comp : Wk n m → Wk m l → Wk n l
  | Wk.id, σ => σ
  | Wk.step ρ, σ => Wk.step (wk_comp ρ σ)

/-- info: (some wk_comp.eq_def) -/
#guard_msgs in
#eval tst ``wk_comp

#check @wk_comp.eq_1
#check @wk_comp.eq_2
#check @wk_comp.eq_def
