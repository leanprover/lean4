import Lean

open Lean Meta

def ex1 (declName : Name) : MetaM Unit := do
  let info ← getConstInfo declName
  IO.println s!"{declName} : {← ppExpr info.type}"
  if let some val := info.value? then 
    IO.println s!"{declName} : {← ppExpr val}"
    
#eval ex1 ``Nat

def ex2 (declName : Name) : MetaM Unit := do
  let info ← getConstInfo declName
  trace[Meta.debug] "{declName} : {info.type}"
  if let some val := info.value? then 
    trace[Meta.debug] "{declName} : {val}"

#eval ex2 ``Add.add

set_option trace.Meta.debug true in
#eval ex2 ``Add.add

def ex3 (declName : Name) : MetaM Unit := do
  let info ← getConstInfo declName
  forallTelescope info.type fun xs type => do
    trace[Meta.debug] "hypotheses : {xs}"
    trace[Meta.debug] "resultType : {type}"
    for x in xs do
      trace[Meta.debug] "{x} : {← inferType x}"

def myMin [LT α] [DecidableRel (α := α) (·<·)] (a b : α) : α :=
  if a < b then 
    a
  else 
    b

set_option trace.Meta.debug true in
#eval ex3 ``myMin

def ex4 : MetaM Unit := do
  let nat := mkConst ``Nat
  withLocalDeclD `a nat fun a => 
  withLocalDeclD `b nat fun b => do
    let e ← mkAppM ``HAdd.hAdd #[a, b]
    trace[Meta.debug] "{e} : {← inferType e}"
    let e ← mkAdd a (mkNatLit 5)
    trace[Meta.debug] "added 5: {e}"
    let e ← whnf e
    trace[Meta.debug] "whnf: {e}"
    let e ← reduce e
    trace[Meta.debug] "reduced: {e}"
    let a_plus_1 ← mkAdd a (mkNatLit 1)
    let succ_a   := mkApp (mkConst ``Nat.succ) a
    trace[Meta.debug] "({a_plus_1} =?= {succ_a}) == {← isDefEq a_plus_1 succ_a}"
    let m ← mkFreshExprMVar nat
    let m_plus_1 ← mkAdd m (mkNatLit 1)
    trace[Meta.debug] "m_plus_1: {m_plus_1}"
    unless (← isDefEq m_plus_1 succ_a) do throwError "isDefEq failed"
    trace[Meta.debug] "m_plus_1: {m_plus_1}"

set_option trace.Meta.debug true in
#eval ex4

open Elab Term

def ex5 : TermElabM Unit := do
  let nat := Lean.mkConst ``Nat
  withLocalDeclD `a nat fun a => do 
  withLocalDeclD `b nat fun b => do
    let ab ← mkAppM ``HAdd.hAdd #[a, b]
    let stx ← `(fun x => if x < 10 then $(← exprToSyntax ab) + x else x + $(← exprToSyntax a))
    let e ← elabTerm stx none
    trace[Meta.debug] "{e} : {← inferType e}"
    let e := mkApp e (mkNatLit 5)
    let e ← whnf e
    trace[Meta.debug] "{e}"
       
set_option trace.Meta.debug true in
#eval ex5
