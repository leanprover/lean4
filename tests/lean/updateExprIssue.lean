import Lean

open Lean

unsafe def tst1 : MetaM Unit := do
  let e  := mkApp (mkSort levelZero) (mkSort levelZero)
  let e' := e.updateApp! (mkSort levelZero) (mkSort levelZero)
  assert! ptrAddrUnsafe e == ptrAddrUnsafe e'
  let e' := e.replace fun _ => none
  assert! ptrAddrUnsafe e == ptrAddrUnsafe e'

#eval tst1

set_option trace.compiler.ir.init true
def sefFn (e : Expr) (f : Expr) : Expr :=
  match e with
  | .app _ a _ => e.updateApp! f a
  | _ => e
