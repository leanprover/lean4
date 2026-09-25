/-!
Regression test for #15037: a lambda's instance binder is used in a later binder type.
-/

universe u

set_option linter.unusedVariables false

class E (α : Type u) [BEq α] : Prop where
  h : True

def g : {α : Type u} → [BEq α] → (x : E α → Nat) → Nat :=
  fun {α} [BEq α] (x : E α → Nat) => 0

/--
info: def g.{u} : {α : Type u} → [inst : BEq.{u} α] → (x : @E.{u} α inst → Nat) → Nat :=
fun {α : Type u} [inst : BEq.{u} α] (x : @E.{u} α inst → Nat) => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))
-/
#guard_msgs in
set_option pp.all true in
#print g
