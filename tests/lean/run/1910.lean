/-!
# Dot notation and CoeFun

https://github.com/leanprover/lean4/issues/1910
-/

set_option pp.mvars false

/-!
Test that dot notation resolution can see through CoeFun instances.
-/

structure Equiv (α β : Sort _) where
  toFun : α → β
  invFun : β → α

infixl:25 " ≃ " => Equiv

instance : CoeFun (α ≃ β) fun _ => α → β where
  coe := Equiv.toFun

structure Foo where
  n : Nat

def Foo.n' : Foo ≃ Nat := ⟨Foo.n, Foo.mk⟩

variable (f : Foo)
/-- info: Foo.n'.toFun f : Nat -/
#guard_msgs in #check f.n'

example (f : Foo) : f.n' = f.n := rfl

/-!
Fail dot notation if it requires using a named argument from the CoeFun instance.
-/
structure F where
  f : Bool → Nat → Nat

instance : CoeFun F (fun _ => (x : Bool) → (y : Nat) → Nat) where
  coe x := fun (a : Bool) (b : Nat) => x.f a b

-- Recall CoeFun oddity: it uses the unfolded *value* to figure out parameter names.
-- That's why this is `a` and `b` rather than `x` and `y`.
/-- info: fun x => (fun a b => x.f a b) true 2 : F → Nat -/
#guard_msgs in #check fun (x : F) => x (a := true) (b := 2)

def Nat.foo : F := { f := fun _ b => b }

-- Ok:
/-- info: fun n x => (fun a b => Nat.foo.f a b) x n : Nat → Bool → Nat -/
#guard_msgs in #check fun (n : Nat) => (Nat.foo · n)

-- Intentionally fails:
/--
error: invalid field notation, function 'Nat.foo' has argument with the expected type
  Nat
but it cannot be used
---
info: fun n => sorry : (n : Nat) → ?_ n
-/
#guard_msgs in #check fun (n : Nat) => n.foo

/-!
Make sure that dot notation does not use the wrong CoeFun instance.
The following instances rely on the second one having higher priority,
so we need to fail completely when the instances would depend on argument values.
-/

structure Bar (b : Bool) where

instance : CoeFun (Bar b) (fun _ => Bar b → Bool) where
  coe := fun _ _ => b

instance : CoeFun (Bar true) (fun _ => (b : Bool) → Bar b) where
  coe := fun _ _ => {}

def Bar.bar : Bar true := {}

/-- info: fun f => (fun x => false) f : Bar false → Bool -/
#guard_msgs in #check fun (f : Bar false) => Bar.bar false f
/--
error: invalid field notation, function 'Bar.bar' does not have argument with type (Bar ...) that can be used, it must be explicit or implicit with a unique name
---
info: fun f => sorry : (f : Bar false) → ?_ f
-/
#guard_msgs in #check fun (f : Bar false) => f.bar false

/-- info: fun f => (fun x => false) f : Bar false → Bool -/
#guard_msgs in #check fun (f : Bar false) => Bar.bar true false f
/--
error: invalid field notation, function 'Bar.bar' does not have argument with type (Bar ...) that can be used, it must be explicit or implicit with a unique name
---
info: fun f => sorry : (f : Bar false) → ?_ f
-/
#guard_msgs in #check fun (f : Bar false) => f.bar true false
