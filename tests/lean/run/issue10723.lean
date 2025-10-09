import Lean.Syntax

open Lean

mutual
def isEmpty : Syntax → Bool
  | .node _ _ xs =>
    xs.all isEmpty
  | _ => false
termination_by s => s
decreasing_by sorry

def onlyIdent : Syntax → Bool
  | .node _ _ args =>
    let nonEmpty := args.filter (!isEmpty ·)
    if h : nonEmpty.size = 1 then onlyIdent nonEmpty[0]
    else false
  | .ident .. => true
  | _ => false
termination_by s => s
decreasing_by sorry
end

private partial def onlyIdent' : Syntax → Bool
  | .node _ _ args =>
    let nonEmpty := args.filter (!isEmpty ·)
    if h : nonEmpty.size = 1 then onlyIdent nonEmpty[0]
    else false
  | .ident .. => true
  | _ => false
where
  isEmpty : Syntax → Bool
  | .node _ _ xs =>
    xs.all isEmpty
  | _ => false
