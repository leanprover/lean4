/-
The current plan is to allow instances to have preconditions with registered tactics.
Typeclass resolution will delay these proof obligations, effectively assuming that they will succeed.
If typeclass resolution succeeds, it will return a list of (mvar, lctx) pairs to the elaborator,
which will try to synthesize the proofs and throw a good error message if it fails.
-/

class Foo (b : Bool) : Type

class FooTrue (b : Bool) extends Foo b : Type :=
(H : b = true)

/- This requires the tactic framework and auto_param. -/
-- @[instance] axiom CoeFooFooTrue (b : Bool) (H : b = true . refl) : HasCoe (Foo b) (FooTrue b)

instance BoolToFoo (b : Bool) : Foo b := Foo.mk b

def forceFooTrue (b : Bool) (fooTrue : FooTrue b) : Bool := b

/- Should succeed (once CoeFooFooTrue can be written) -/
#check forceFooTrue true (Foo.mk true)

/- Should fail (even after CoeFooFooTrue can be written -/
#check forceFooTrue false (Foo.mk false)

/-
This plan has one limitation, that has so far been deemed acceptable:
it will not support classes with different instances depending on the provability of preconditions.
The classic example is multiplying two elements of `ℤ/nℤ` where `n` is not prime.
Here is a toy version of this problem:

<<
@[class] axiom Prime (p : Nat) : Prop

@[instance] axiom p2 : Prime 2
@[instance] axiom p3 : Prime 3

@[class] axiom Field : Type → Type
@[class] axiom Ring : Type → Type

@[instance] axiom FieldToDiv (α : Type) [Field α] : Div α
@[instance] axiom FieldToMul (α : Type) [Field α] : Mul α
@[instance] axiom RingToMul (α : Type) [Ring α] : Mul α

axiom mkType : Nat → Type

@[instance] axiom PrimeField (n : Nat) (Hp : Prime n . provePrimality) : Field (mkType n)
@[instance] axiom NonPrimeRing (n : Nat) : Ring (mkType n)

example (α β : mkType 4) : α * β = β * α
>>

The issue is that (depending on the order the instances are tried),
the instance involving `FieldToMul` will succeed in typeclass resolution,
but the proof will fail later on.

I (@dselsam) still thinks this plan is a good compromise.
For examples like this, the definition in question (i.e. `Prime`) can be made a class instead
and taken as an inst-implicit argument to `PrimeField`.
-/
