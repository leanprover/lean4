import Lean.Syntax

open Lean

private partial def onlyIdent' : Syntax → Bool
  | .node _ _ args =>
    let nonEmpty := args.filter (!isEmpty ·)
    if h : nonEmpty.size = 1 then onlyIdent' nonEmpty[0]
    else false
  | .ident .. => true
  | _ => false
where
  isEmpty : Syntax → Bool
  | .node _ _ xs =>
    xs.all isEmpty
  | _ => false

partial def onlyIdent'' : Syntax → Bool
  | .node _ _ args =>
    let nonEmpty := args.filter (!isEmpty () ·)
    if h : nonEmpty.size = 1 then onlyIdent'' nonEmpty[0]
    else false
  | .ident .. => true
  | _ => false
where
  isEmpty : Unit → Syntax → Bool
  | _, .node _ _ xs =>
    xs.all (isEmpty ())
  | _, _ => false
