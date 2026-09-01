import Lean

open Lean

unsafe def tst1 : MetaM Unit := do
  let e  := mkApp (mkSort Level.zero) (mkSort Level.zero)
  let e' := e.updateApp! (mkSort Level.zero) (mkSort Level.zero)
  assert! ptrAddrUnsafe e == ptrAddrUnsafe e'
  let e' := e.replace fun _ => none
  assert! ptrAddrUnsafe e == ptrAddrUnsafe e'

#eval tst1

set_option trace.Compiler.saveMono true
def sefFn (e : Expr) (f : Expr) : Expr :=
  match e with
  | .app _ a => e.updateApp! f a
  | _ => e
