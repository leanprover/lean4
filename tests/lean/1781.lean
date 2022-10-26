import Lean.Elab.ElabRules
syntax "kdef " ident (".{" ident,+ "}")? " : " term " := " term : command

open Lean Elab Command Term in
elab_rules : command | `(kdef $name $[.{ $levelParams?,* }]? : $type := $value) => do
  let levelParams :=
    if let some levelParams := levelParams?
    then levelParams.getElems.toList.map (·.getId)
    else []
  let (type, value) ← runTermElabM fun _ => do
    setLevelNames levelParams
    let type ← elabTermAndSynthesize type none
    let value ← elabTermAndSynthesize value none
    return (type, value)
  liftCoreM <| addDecl <| .defnDecl {
    name := name.getId
    levelParams
    type
    value
    hints := .abbrev
    safety := .safe
  }

kdef Univ'.{u} : Sort (imax 1 u + 1) := Sort (imax 1 u + 1)
def Univ := Univ'.{0}
#check (Univ : Univ) -- !!!

example : Sort (imax u v + 1) := Unit → Sort (imax u v)
-- (kernel) declaration type mismatch, '_example' has type
--   Type (max 0 (imax u v))
-- but it is expected to have type
--   Type (imax u v)
