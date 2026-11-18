import Lean

/-!
Tests that type class resolution reports a goal as stuck without searching where an argument that is
a type is a metavariable, and that it still fails where there is no instance to try.
-/

open Lean Meta

class C (α : Type) where
instance : C Nat := ⟨⟩
instance : C Bool := ⟨⟩

class D (α : Type) where
instance : D α := ⟨⟩

class E (α β : Type) where
instance : E Nat Nat := ⟨⟩

class F (α : Type) where
instance instFNat : F Nat := ⟨⟩
attribute [-instance] instFNat

def toStr : LOption Expr → String
  | .some _ => "some"
  | .none => "none"
  | .undef => "stuck"

/-- Synthesizes `mk ?α` for a fresh `?α : Type`. -/
def synth (mk : Expr → Expr) : MetaM String := do
  let α ← mkFreshExprMVar (mkSort 1)
  return toStr (← trySynthInstance (mk α))

-- Stuck on `?α`.
/-- info: "stuck" -/
#guard_msgs in
#eval synth (mkApp (mkConst ``C))

-- Also where an instance applies to any `?α`: the goal is resolved once `?α` is assigned.
/-- info: "stuck" -/
#guard_msgs in
#eval synth (mkApp (mkConst ``D))

-- No instance unifies with the other argument: a failure, not stuck.
/-- info: "none" -/
#guard_msgs in
#eval synth (mkApp2 (mkConst ``E) · (mkConst ``Bool))

/-- info: "stuck" -/
#guard_msgs in
#eval synth (mkApp2 (mkConst ``E) · (mkConst ``Nat))

/-- info: "stuck" -/
#guard_msgs in
#eval synth (mkApp2 (mkConst ``E) (mkConst ``Nat))

-- The only instance is erased: a failure, not stuck.
/-- info: "none" -/
#guard_msgs in
#eval synth (mkApp (mkConst ``F))

-- A nested metavariable.
/-- info: "none" -/
#guard_msgs in
#eval synth fun α => mkApp (mkConst ``C) (mkApp (mkConst ``List [0]) α)

-- A local instance is an instance to try.
/-- info: "stuck" -/
#guard_msgs in
#eval show MetaM String from do
  withLocalDeclD `β (mkSort 1) fun β =>
  withLocalDecl `inst .instImplicit (mkApp (mkConst ``F) β) fun _ =>
  synth (mkApp (mkConst ``F))

/-- info: "stuck" -/
#guard_msgs in
#eval show MetaM String from do
  let α ← mkFreshExprMVar (mkSort 1)
  withLocalDecl `inst .instImplicit (mkApp (mkConst ``F) α) fun _ =>
  return toStr (← trySynthInstance (mkApp (mkConst ``F) α))

class G (n : Nat) where
instance : G n := ⟨⟩

-- A metavariable that is not a type does not prevent the search.
/-- info: "some" -/
#guard_msgs in
#eval show MetaM String from do
  let n ← mkFreshExprMVar (mkConst ``Nat)
  return toStr (← trySynthInstance (mkApp (mkConst ``G) n))

/--
error: typeclass instance problem is stuck, it is often due to metavariables
  C ?m.5
-/
#guard_msgs in
example := (inferInstance : C _)

/--
error: failed to synthesize instance of type class
  E ?m.2 Bool

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example := (inferInstance : E _ Bool)
