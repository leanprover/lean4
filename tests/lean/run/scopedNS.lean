module
/-
Tests for scoping syntax to a specific namespace using `scoped[NS]`
-/


-- Test 1: Scoped notation in a different namespace
namespace A

scoped[B] postfix:1024 " !" => Nat.succ

end A

-- The notation should be accessible when opening B
open B
#guard (5 ! = 6)

-- Test 2: Scoped infix notation
scoped[Math] infix:65 " ⊕ " => Nat.add

/-- info: 7 -/
#guard_msgs in
open Math in
#eval 3 ⊕ 4

/--
error: failed to synthesize instance of type class
  OfNat (Type _) 3
numerals are polymorphic in Lean, but the numeral `3` cannot be used in a context where the expected type is
  Type _
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
error: failed to synthesize instance of type class
  OfNat (Type _) 4
numerals are polymorphic in Lean, but the numeral `4` cannot be used in a context where the expected type is
  Type _
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
error: cannot evaluate, types are not computationally relevant
-/
#guard_msgs in
set_option pp.mvars false in
#eval 3 ⊕ 4


-- Test 3: Scoped attribute
def myInstance : Inhabited Nat := ⟨42⟩

scoped[MyNS] attribute [instance] myInstance

/-- info: 42 -/
#guard_msgs in
open MyNS in
#eval (default : Nat)

/-- info: 0 -/
#guard_msgs in
#eval (default : Nat)
