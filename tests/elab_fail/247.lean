import Lean

namespace Lean.Meta

def f (e : Expr) : MetaM Bool := do
  forallTelescope e fun xs b =>
    match (← uinfoldDefinition? b) with
    | none   => pure true
    | some _ => pure false

end Lean.Meta
