import Lean
open Lean Lean.PrettyPrinter

def pfoo : PUnit → PUnit := id
def px   : PUnit := ()

@[appUnexpander foo] def unexpandFoo : Unexpander := fun _ => `(sorry)

#eval show MetaM Format from do
  let e : Expr := mkApp (mkMData {} $ mkConst `foo [levelOne]) (mkConst `x)
  formatTerm (← delab Name.anonymous [] e)

#eval show MetaM Format from do
  let opts := ({}: Options).setBool `pp.universes true
  -- the MData annotation should make it not a regular application,
  -- so the unexpander should not be called.
  let e : Expr := mkApp (mkMData opts $ mkConst `foo [levelOne]) (mkConst `x)
  formatTerm (← delab Name.anonymous [] e)
