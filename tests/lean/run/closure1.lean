import Lean
open Lean
open Lean.Meta

universes u

inductive Vec (α : Type u) : Nat → Type u
| nil      : Vec 0
| cons {n} : α → Vec n → Vec (n+1)

set_option trace.Meta.debug true

def mkArrow (d b : Expr) : Expr := mkForall `_ BinderInfo.default d b

def printDef (declName : Name) : MetaM Unit := do
cinfo ← getConstInfo declName;
trace! `Meta.debug cinfo.value!

def tst1 : MetaM Unit := do
let u := mkLevelParam `u;
let v := mkLevelMVar  `v;
m1 ← mkFreshExprMVar (mkSort levelOne);
withLocalDeclD `α (mkSort u) $ fun α => do
withLocalDeclD `β (mkSort v) $ fun β => do
m2 ← mkFreshExprMVar (mkArrow α m1);
withLocalDeclD `a α $ fun a => do
withLocalDeclD `f (mkArrow α α) $ fun f => do
withLetDecl   `b α (mkApp f a) $ fun b => do
let t := mkApp m2 (mkApp f b);
e ← mkAuxDefinitionFor `foo1 t;
trace! `Meta.debug e;
printDef `foo1;
pure ()

#eval tst1

def tst2 : MetaM Unit := do
let u := mkLevelParam `u;
withLocalDeclD `α (mkSort (mkLevelSucc u)) $ fun α => do
withLocalDeclD `v1 (mkApp2 (mkConst `Vec [u]) α (mkNatLit 10)) $ fun v1 =>
withLetDecl `n (mkConst `Nat) (mkNatLit 10) $ fun n =>
withLocalDeclD `v2 (mkApp2 (mkConst `Vec [u]) α n) $ fun v2 => do
m ← mkFreshExprMVar (mkArrow (mkApp2 (mkConst `Vec [u]) α (mkNatLit 10)) (mkSort levelZero));
withLocalDeclD `p (mkSort levelZero) $ fun p => do
t ← mkEq v1 v2;
let t := mkApp2 (mkConst `And) t (mkApp2 (mkConst `Or) (mkApp m v2) p);
e ← mkAuxDefinitionFor `foo2 t;
trace! `Meta.debug e;
printDef `foo2;
pure ()

#eval tst2
