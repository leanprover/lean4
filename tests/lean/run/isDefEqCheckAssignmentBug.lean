import Lean

open Lean
open Lean.Meta

def f (x : Type) := x

def tst : MetaM Unit := do
  let m1 ← mkFreshExprMVar none
  withLocalDeclD `x m1 fun x => do
    trace[Meta.debug] "{x} : {← inferType x}"
    trace[Meta.debug] "{m1} : {← inferType m1}"
    let m2 ← mkFreshExprMVar (mkSort levelOne)
    let t  ← mkAppM ``f #[m2]
    trace[Meta.debug] "{m2} : {← inferType m2}"
    unless (← fullApproxDefEq <| isDefEq m1 t) do  -- m1 := f m3 -- where `m3` has a smaller scope than `m2`
      throwError "isDefEq failed"
    trace[Meta.debug] "{m2} : {← inferType m2}"
    trace[Meta.debug] "{m1} : {← inferType m1}"
    let e ← mkForallFVars #[x] m2 -- `forall (x : f ?m2), ?m2`
    trace[Meta.debug] "{e} : {← e}"
    return ()

set_option trace.Meta.isDefEq true
set_option trace.Meta.debug true
#eval tst
