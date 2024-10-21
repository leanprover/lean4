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
  Nat → True : Prop
-/
#guard_msgs in
#check (1 : ∀ (n : Nat), True)

/--
error: failed to synthesize
  OfNat String 1
numerals are polymorphic in Lean, but the numeral `1` cannot be used in a context where the expected type is
  String
due to the absence of the instance above
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#check (1 : String)

/--
error: failed to synthesize
  OfNat Bool 1
numerals are polymorphic in Lean, but the numeral `1` cannot be used in a context where the expected type is
  Bool
due to the absence of the instance above
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#check (1 : Bool)

/--
error: failed to synthesize
  OfNat (Bool → Nat) 1
numerals are polymorphic in Lean, but the numeral `1` cannot be used in a context where the expected type is
  Bool → Nat
due to the absence of the instance above
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#check (1 : Bool → Nat)

/--
error: failed to synthesize
  OfNat String 0
numerals are polymorphic in Lean, but the numeral `0` cannot be used in a context where the expected type is
  String
due to the absence of the instance above
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
def foo : String :=
  let x := 0
  x ++ x
