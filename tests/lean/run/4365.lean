universe u

/--
error: numerals are data in Lean, but the expected type is a proposition
  True : Prop
-/
#guard_msgs in
#check (1 : True)

/--
error: numerals are data in Lean, but the expected type is universe polymorphic and may be a proposition
  α : Sort u
-/
#guard_msgs in
def f (α : Sort u) : α :=
  1

/--
error: numerals are data in Lean, but the expected type is universe polymorphic and may be a proposition
  α : Sort u
---
info: fun {α} => id (id sorry) : {α : Sort u} → α
-/
#guard_msgs in
#check fun {α : Sort u} => id (α := α) (id 0)

/--
error: numerals are data in Lean, but the expected type is a proposition
  ∀ (n : Nat), True : Prop
-/
#guard_msgs in
#check (1 : ∀ (n : Nat), True)

/--
error: failed to synthesize instance of type class
  OfNat String 1
numerals are polymorphic in Lean, but the numeral `1` cannot be used in a context where the expected type is
  String
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#check (1 : String)

/--
error: failed to synthesize instance of type class
  OfNat Bool 1
numerals are polymorphic in Lean, but the numeral `1` cannot be used in a context where the expected type is
  Bool
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#check (1 : Bool)

/--
error: failed to synthesize instance of type class
  OfNat (Bool → Nat) 1
numerals are polymorphic in Lean, but the numeral `1` cannot be used in a context where the expected type is
  Bool → Nat
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#check (1 : Bool → Nat)

/--
error: failed to synthesize instance of type class
  OfNat String 0
numerals are polymorphic in Lean, but the numeral `0` cannot be used in a context where the expected type is
  String
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
def foo : String :=
  let x := 0
  x ++ x
