import Lean

def f1 (x : Nat) : Except String Nat :=
  if x > 0 then
    .ok x
  else
    .error "argument is zero"

namespace Lean.Elab
open Lsp

def identOf : Info → Option (RefIdent × Bool)
  | .ofTermInfo ti => match ti.expr with
    | .const n .. => some (.const n, ti.isBinder)
    | .fvar id .. => some (.fvar id, ti.isBinder)
    | _ => none
  | .ofFieldInfo fi => some (.const fi.projName, false)
  | _ => none

def isConst (e : Expr) : Bool :=
  e matches .const ..

def isImplicit (bi : BinderInfo) : Bool :=
  bi matches .implicit

end Lean.Elab

def f2 (xs : List Nat) : List Nat :=
  .map (· + 1) xs

def f3 : Nat :=
  .zero

def f4 (x : Nat) : Nat :=
  .succ x
