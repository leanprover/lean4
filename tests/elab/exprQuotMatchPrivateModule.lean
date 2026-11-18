module

public import Init
import Lean

/-!
Module-system tests for `expr` quotation auxiliary pattern constants inside a `module` file
with a private `import Lean`.
-/

open Lean Meta

namespace ExprQuotMatchPrivateModule

private meta def check (cond : Bool) (msg : String) : MetaM Unit := do
  unless cond do
    throwError msg

private meta def privMetaWithPrivateLean (e : Expr) : MetaM (Option (Expr × Expr)) :=
  match e with
  | `(expr| ?a + ?b) => return some (a, b)
  | _ => return none

meta section

private def privInMetaSection (e : Expr) : MetaM Bool := do
  if let `(expr/defeq| 1 + 1) := e then
    return true
  else
    return false

end

#guard_msgs in
#eval show MetaM Unit from do
  let one := mkNatLit 1
  check ((← privMetaWithPrivateLean (mkNatAdd one one)) == some (one, one))
    "privMetaWithPrivateLean failed"
  check (← privInMetaSection (mkNatAdd one one)) "privInMetaSection failed"

end ExprQuotMatchPrivateModule
