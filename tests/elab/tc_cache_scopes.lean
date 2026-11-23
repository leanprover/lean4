import Lean

/-!
Changes to the instances, unification hints and reducibility statuses in effect invalidate the type
class resolution cache entries that depended on them. Note that `Meta.modifyEnv` always clears the
cache, whereas operations at `CoreM` level and commands run through `liftCommandElabM` (tested here)
do not.
-/

open Lean Meta Elab Command

structure Magma where
  α   : Type
  mul : α → α → α

def Nat.Magma : Magma := ⟨Nat, Nat.mul⟩

class K2 (α β : Type) where

instance (α : Type) : K2 α α := ⟨⟩

namespace Algebra
scoped unif_hint (s : Magma) where
  s =?= Nat.Magma |- s.α =?= Nat
end Algebra

/-- Resolves `K2 Nat.Magma.α Nat` only with the scoped hint. -/
def hintQuery : Expr :=
  mkApp2 (mkConst ``K2) (mkApp (mkConst ``Magma.α) (mkConst ``Nat.Magma)) (mkConst ``Nat)

/-- info: false true false -/
#guard_msgs in
run_meta do
  let before := (← synthInstance? hintQuery).isSome
  (pushScope : CoreM Unit)
  (activateScoped `Algebra : CoreM Unit)
  let active := (← synthInstance? hintQuery).isSome
  (popScope : CoreM Unit)
  let after := (← synthInstance? hintQuery).isSome
  logInfo m!"{before} {active} {after}"

class K (α : Type) where

namespace Foo
scoped instance : K Nat := ⟨⟩
end Foo

def instQuery : Expr := mkApp (mkConst ``K) (mkConst ``Nat)

/-- info: false true false -/
#guard_msgs in
run_meta do
  let before := (← synthInstance? instQuery).isSome
  (pushScope : CoreM Unit)
  (activateScoped `Foo : CoreM Unit)
  let active := (← synthInstance? instQuery).isSome
  (popScope : CoreM Unit)
  let after := (← synthInstance? instQuery).isSome
  logInfo m!"{before} {active} {after}"

class K3 (α : Type) where

/-- info: false true -/
#guard_msgs in
run_meta do
  let q := mkApp (mkConst ``K3) (mkConst ``Nat)
  let before := (← synthInstance? q).isSome
  liftCommandElabM <| elabCommand (← `(instance : K3 Nat := ⟨⟩))
  let after := (← synthInstance? q).isSome
  logInfo m!"{before} {after}"

class KR (α : Type) where

instance : KR Nat := ⟨⟩

def T := Nat

namespace Bar
set_option allowUnsafeReducibility true in
attribute [scoped reducible] T
end Bar

/-- Resolves `KR T` only while `T` is reducible. -/
def reducibilityQuery : Expr := mkApp (mkConst ``KR) (mkConst ``T)

/-- info: false true false -/
#guard_msgs in
run_meta do
  let before := (← synthInstance? reducibilityQuery).isSome
  (pushScope : CoreM Unit)
  (activateScoped `Bar : CoreM Unit)
  let active := (← synthInstance? reducibilityQuery).isSome
  (popScope : CoreM Unit)
  let after := (← synthInstance? reducibilityQuery).isSome
  logInfo m!"{before} {active} {after}"
