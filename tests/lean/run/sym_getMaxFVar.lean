import Lean.Meta.Sym
open Lean Meta Sym
open Internal
def checkMaxFVar (e : Expr) (x : Expr) : SymM Unit := do
  let some fvarId ← getMaxFVar? e | unreachable!
  assert! x.fvarId! == fvarId

def test1 : MetaM Unit := do
  let nat := mkConst ``Nat
  withLocalDeclD `x nat fun x => do
  let m₁ ← mkFreshExprMVar nat
  withLocalDeclD `y nat fun y => do
  let m₂ ← mkFreshExprMVar nat
  withLocalDeclD `z nat fun z => do
  SymM.run do
  let x ← shareCommon x
  let y ← shareCommon y
  let z ← shareCommon z
  let m₁ ← shareCommon m₁
  let m₂ ← shareCommon m₂
  let f ← mkConstS `f
  let e₁ ← mkAppS f x
  checkMaxFVar e₁ x
  let e₂ ← mkAppS e₁ m₁
  checkMaxFVar e₂ x
  let e₂ ← mkAppS e₁ m₂
  checkMaxFVar e₂ y
  let e₃ ← mkAppS e₂ (← mkProjS ``Prod 0 (← mkAppS f z))
  checkMaxFVar e₃ z
  let e₄ ← mkAppS f (← shareCommon (mkNatLit 3))
  assert! (← getMaxFVar? e₄).isNone

#eval test1
