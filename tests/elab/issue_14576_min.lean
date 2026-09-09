import Lean
open Lean Elab Command

structure C where b : Bool
inductive W : Type where | mk (p : Bool)
inductive L (α : Type) (b : Bool) : Type where | mk

meta def build : CommandElabM Unit := do
  let w := mkBVar 0
  let Ew := mkApp (mkConst `E) w
  let b := mkProj ``C 0 (mkProj ``C 0 w)
  let l := mkApp2 (mkConst ``L) Ew b
  let Et := mkForall `w .default (mkConst ``W) (mkSort 1)
  let ct := mkForall `w .default (mkConst ``W) <|
    mkForall `l .default l (mkApp (mkConst `E) (mkBVar 1))
  logInfo ct
  liftCoreM <| addDecl <| .inductDecl [] 1 [{
    name := `E, type := Et, ctors := [{ name := `E.mk, type := ct }] }] false
  logInfo "E accepted"

elab "mkbug" : command => build

/--
info: (w : W) → L (E w) w.1.1 → E w
---
error: (kernel) invalid projection
  w.1
-/
#guard_msgs in
mkbug
