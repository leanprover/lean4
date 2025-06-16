/-!
# Add explicit mode projections

This is to fix a bug where structure instance notation was not working when there were opt params.
-/

/-!
Motivating issue from https://github.com/leanprover/lean4/issues/5406
The `example` had an elaboration error because the structure instance was expanding to `{b := m.b, x := 1}`.
Now it expands to `{b := @m.b, x := 1}`.
-/
structure Methods where
  b : Nat → (opt : Nat := 42) → Nat
  x : Nat

example (m : Methods) : Methods := { m with x := 1 }

/-- info: fun m => { b := @Methods.b m, x := 1 } : Methods → Methods -/
#guard_msgs in #check fun (m : Methods) => { m with x := 1 }


/-!
Tests of explicit mode, with and without arguments.
-/

/-- info: fun m => @Methods.b m : Methods → Nat → optParam Nat 42 → Nat -/
#guard_msgs in #check fun (m : Methods) => @m.b

/-- info: fun m => @Methods.b m : Methods → Nat → optParam Nat 42 → Nat -/
#guard_msgs in #check fun (m : Methods) => @(m).b

/-- info: fun m => @Methods.b m : Methods → Nat → optParam Nat 42 → Nat -/
#guard_msgs in #check fun (m : Methods) => @m.1

/-- info: fun m => @Methods.b m : Methods → Nat → optParam Nat 42 → Nat -/
#guard_msgs in #check fun (m : Methods) => @(m).1

/-- info: fun m => @Methods.b m 1 : Methods → optParam Nat 42 → Nat -/
#guard_msgs in #check fun (m : Methods) => @m.b 1

/-- info: fun m => @Methods.b m 1 : Methods → optParam Nat 42 → Nat -/
#guard_msgs in #check fun (m : Methods) => @(m).b 1

/-- info: fun m => @Methods.b m 1 : Methods → optParam Nat 42 → Nat -/
#guard_msgs in #check fun (m : Methods) => @m.1 1

/-- info: fun m => @Methods.b m 1 : Methods → optParam Nat 42 → Nat -/
#guard_msgs in #check fun (m : Methods) => @(m).1 1


/-!
Tests of explicit mode with class instances. The type parameter remains implicit.
We need this so that structure instances work properly.
-/

class C (α : Type) [Inhabited α] where
  f (x : α := default) : α
  x : Nat

/-- info: fun inst => C.f : C Nat → Nat -/
#guard_msgs in #check fun (inst : C Nat) => inst.f

/-- info: fun inst => @C.f Nat instInhabitedNat inst : C Nat → optParam Nat default → Nat -/
#guard_msgs in #check fun (inst : C Nat) => @inst.f

/-- info: fun inst => @C.f Nat instInhabitedNat inst : C Nat → optParam Nat default → Nat -/
#guard_msgs in #check fun (inst : C Nat) => @C.f _ _ inst

/-- info: fun inst => { f := @C.f Nat instInhabitedNat inst, x := 1 } : C Nat → C Nat -/
#guard_msgs in #check fun (inst : C Nat) => { inst with x := 1 }


/-!
Tests of deeper updates and accesses.
-/

structure A (α : Type) where
  x : α
structure B (α β : Type) extends A α where
  y : β

/-- info: fun α β x' b => { x := x', y := b.y } : (α β : Type) → α → B α β → B α β -/
#guard_msgs in #check fun (α β) (x' : α) (b : B α β) => {b with x := x'}

/-- info: fun α β b => b.x : (α β : Type) → B α β → α -/
#guard_msgs in #check fun (α β) (b : B α β) => @b.toA.x

/-- info: fun α β b => b.x : (α β : Type) → B α β → α -/
#guard_msgs in #check fun (α β) (b : B α β) => @b.x


/-!
Tests of implicit arguments in updates.
-/

structure I where
  f : {_ : Nat} → Nat
  x := 1

-- used to give `fun i ↦ ?m.369 i : I → I`
/-- info: fun i => { f := @I.f i } : I → I -/
#guard_msgs in #check fun (i : I) => {i with x := 1 }
