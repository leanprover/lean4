import Lean

open Lean
open Lean.Meta

universe u

inductive Vec (α : Type u) : Nat → Type u
| nil      : Vec α 0
| cons {n} : α → Vec α n → Vec α (n+1)

set_option trace.Meta.debug true

def printDef (declName : Name) : MetaM Unit := do
let cinfo ← getConstInfo declName;
trace[Meta.debug] cinfo.value!

instance : Coe Name FVarId where
  coe n := { name := n }

instance : Coe Name MVarId where
  coe n := { name := n }

def tst1 : MetaM Unit := do
let u := mkLevelParam `u
let v := mkLevelMVar  `v
let m1 ← mkFreshExprMVar (mkSort levelOne)
withLocalDeclD `α (mkSort u) $ fun α => do
withLocalDeclD `β (mkSort v) $ fun β => do
let m2 ← mkFreshExprMVar (← mkArrow α m1)
withLocalDeclD `a α $ fun a => do
withLocalDeclD `f (← mkArrow α α) $ fun f => do
withLetDecl   `b α (mkApp f a) $ fun b => do
let t := mkApp m2 (mkApp f b)
let e ← mkAuxDefinitionFor `foo1 t
trace[Meta.debug] e
printDef `foo1

#eval tst1

def tst2 : MetaM Unit := do
let u := mkLevelParam `u
withLocalDeclD `α (mkSort (mkLevelSucc u)) $ fun α => do
withLocalDeclD `v1 (mkApp2 (mkConst `Vec [u]) α (mkNatLit 10)) $ fun v1 =>
withLetDecl `n (mkConst `Nat) (mkNatLit 10) $ fun n =>
withLocalDeclD `v2 (mkApp2 (mkConst `Vec [u]) α n) $ fun v2 => do
let m ← mkFreshExprMVar (← mkArrow (mkApp2 (mkConst `Vec [u]) α (mkNatLit 10)) (mkSort levelZero))
withLocalDeclD `p (mkSort levelZero) $ fun p => do
let t ← mkEq v1 v2
let t := mkApp2 (mkConst `And) t (mkApp2 (mkConst `Or) (mkApp m v2) p)
let e ← mkAuxDefinitionFor `foo2 t
trace[Meta.debug] e
printDef `foo2

#eval tst2
