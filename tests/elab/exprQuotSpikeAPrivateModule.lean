module

public import Init
import Lean

/-!
Spike A tests verifying `exprQuot` auxiliary pattern constants inside a `module` file
with a private `import Lean`.
-/

open Lean Meta

namespace ExprQuotSpikeAPrivateModule

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

#eval show MetaM Unit from do
  let one := mkNatLit 1
  assert! (← privMetaWithPrivateLean (mkNatAdd one one)) == some (one, one)
  assert! (← privInMetaSection (mkNatAdd one one))

end ExprQuotSpikeAPrivateModule
