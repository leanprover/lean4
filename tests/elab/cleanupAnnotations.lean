import Lean

/-!
`Expr.cleanupAnnotations` and `Expr.consumeTypeAnnotations` agree with their previous definitions.
`cleanupAnnotations` removes metadata and the `optParam`, `autoParam`, `outParam`, and
`semiOutParam` annotations at the root only, `consumeTypeAnnotations` removes only the latter, and
both return the expression itself when there is nothing to remove.
-/

open Lean

/-- The previous definition of `Expr.consumeTypeAnnotations`. -/
partial def referenceConsume (e : Expr) : Expr :=
  if e.isOptParam || e.isAutoParam then
    referenceConsume e.appFn!.appArg!
  else if e.isOutParam || e.isSemiOutParam then
    referenceConsume e.appArg!
  else
    e

/-- The previous definition of `Expr.cleanupAnnotations`. -/
partial def reference (e : Expr) : Expr :=
  let e' := referenceConsume e.consumeMData
  if e' == e then e else reference e'

def nat := mkConst ``Nat
def x := mkFVar ⟨`x⟩
def dflt := mkNatLit 0
def md (e : Expr) := mkAnnotation `test e
def opt (α v : Expr) := mkApp2 (mkConst ``optParam [1]) α v
def auto (α t : Expr) := mkApp2 (mkConst ``autoParam [1]) α t
def out (α : Expr) := mkApp (mkConst ``outParam [1]) α
def semiOut (α : Expr) := mkApp (mkConst ``semiOutParam [1]) α

def inputs : List Expr := [
  nat, x, mkSort 1, mkApp (mkConst ``Nat.succ) x, mkApp2 (mkConst ``Nat.add) x x,
  mkApp3 (mkConst ``Eq [1]) nat x x,
  md nat, md (md nat), opt nat dflt, auto nat dflt, out nat, semiOut nat,
  out (opt nat dflt), opt (out nat) dflt, md (out (md (opt (md nat) dflt))), out (md x),
  md (mkApp (mkConst ``Nat.succ) x),
  -- Annotation constants with the wrong number of arguments, or behind metadata.
  mkConst ``outParam [1], mkApp (mkConst ``optParam [1]) nat,
  mkApp3 (mkConst ``optParam [1]) nat dflt x, mkApp2 (mkConst ``outParam [1]) nat x,
  mkApp (md (mkConst ``outParam [1])) nat,
  -- Annotations below the root.
  mkApp (mkConst ``Nat.succ) (out nat), mkForall `a .default nat (out nat)
]

def agrees (e : Expr) : Bool :=
  let r := e.cleanupAnnotations
  let r' := reference e
  r == r' && unsafe (ptrEq r e == ptrEq r' e)

def agreesConsume (e : Expr) : Bool :=
  let r := e.consumeTypeAnnotations
  let r' := referenceConsume e
  r == r' && unsafe (ptrEq r e == ptrEq r' e)

#guard inputs.all agrees
#guard (out (opt nat dflt)).cleanupAnnotations == nat
#guard (md (out (md (opt (md nat) dflt)))).cleanupAnnotations == nat
#guard (mkApp (md (mkConst ``outParam [1])) nat).cleanupAnnotations == mkApp (md (mkConst ``outParam [1])) nat

#guard inputs.all agreesConsume
#guard (out (opt nat dflt)).consumeTypeAnnotations == nat
#guard (md (out nat)).consumeTypeAnnotations == md (out nat)
#guard (out (md (opt nat dflt))).consumeTypeAnnotations == md (opt nat dflt)
