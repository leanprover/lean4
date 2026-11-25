import Lean

/-! Nested proof abstraction preserves application-domain interfaces (#14467). -/

opaque Bytes : Type
opaque Bytes.length : Bytes → Nat

axiom foo {α : Type} (f : α → Bytes) (len : Nat)
    (h : ∀ x, (f x).length = len) : α

def f {len : Nat} (b : { b : Bytes // b.length = len }) : Bytes :=
  b.val

noncomputable def bar (len : Nat) : { b : Bytes // b.length = len } :=
  foo f len (by simp [f])

set_option linter.tacticCheckInstances true

#guard_msgs in
example (len : Nat) : bar len = bar len := by
  unfold bar
  rfl

structure DeferredWitness (α : Type) where
  values : List α
  WF : values.length = values.length := by simp

#guard_msgs in
def DeferredWitness.branch (w : DeferredWitness α) : DeferredWitness α :=
  match w.values with
  | [] => { values := [] }
  | x :: xs => { values := x :: xs }

@[irreducible] def WrappedDefault (n : Nat) : Prop := n = n

structure OpaqueDefault where
  n : Nat
  witness : WrappedDefault n := by unfold WrappedDefault; rfl

open Lean Meta in
run_meta do
  let n ← mkFreshExprMVar (mkConst ``Nat)
  let proof ← mkEqRefl (mkApp2 (mkConst ``Nat.add) n (mkNatLit 0))
  let value := mkApp2 (mkConst ``OpaqueDefault.mk) n proof
  let result ← abstractNestedProofs value (cache := false)
  let actual ← inferType result.appArg!
  let expected := mkApp (mkConst ``WrappedDefault) n
  unless ← isDefEqI actual expected do
    throwError "default proof lost its interface: {actual} instead of {expected}"
  if ← n.mvarId!.isAssigned then
    throwError "default proof comparison assigned the structure argument"
