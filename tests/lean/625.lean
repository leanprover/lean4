import Lean
open Lean Lean.PrettyPrinter

def foo : PUnit → PUnit := id
def x   : PUnit := ()

@[app_unexpander foo] def unexpandFoo : Unexpander := fun _ => `(sorry)

#eval do
  let e : Expr := mkApp (mkMData {} $ mkConst `foo [levelOne]) (mkConst `x)
  formatTerm (← delab e)

#eval do
  let opts := ({}: Options).setBool `pp.universes true
  -- the MData annotation should make it not a regular application,
  -- so the unexpander should not be called.
  let e : Expr := mkApp (mkMData opts $ mkConst `foo [levelOne]) (mkConst `x)
  formatTerm (← delab e)
