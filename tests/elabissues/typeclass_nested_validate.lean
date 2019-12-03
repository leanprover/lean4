/-
This example demonstrates a case where Lean4's tabled typeclass resolution may loop.
It also suggests a workaround, new instance binder semantics, new syntax support, and a new instance validation rule.
-/
#exit

class Field (K : Type) := (u : Unit)
class VectorSpace (K : Type) [Field K] (E : Type) := (u : Unit)
instance VectorSpaceSelf (K : Type) [Field K] : VectorSpace K K := {u:=()}
class CompleteSpace (α : Type) := (u : Unit)
def AlgebraicClosure (K : Type) [Field K] : Type := K

/-
Note that this instance is not a problem when `K` is known,
because it will only ever "unpack" AlgebraicClosures, not create new ones
However, if `K` is ever not known, it will create them ad infinitum!
-/
instance AlgebraicClosure.Field (K : Type) [Field K] : Field (AlgebraicClosure K) := {u:=()}

/-
Here is the "bad" instance one may be tempted to write:

<<
instance bad (K E : Type) [Field K] [VectorSpace K E] [CompleteSpace K] : CompleteSpace E := {u := ()}
>>

It is bad because typeclass resolution will try to find `Field ?K` before it knows what `?K` is,
which in conjunction with the instance `AlgebraicClosure.Field`, will cause resolution to diverge.

Here is the workaround, which is very ugly:

<<
instance veryUgly (K E : Type) {fK : Field K} [@VectorSpace K fK E] [CompleteSpace K] : CompleteSpace E := {u := ()}
>>

Here, `Field ?K` is not solved by typeclass resolution, and instead `VectorSpace ?K ?fK E` will be solved first instead.

With the Lean3 instance semantics, one could make this less ugly by writing
-/
instance ugly (K E : Type) {_ : Field K} [VectorSpace K E] [CompleteSpace K] : CompleteSpace E := {u := ()}

/-
This would work because the `Field K` instance would still be considered for typeclass resolution even though it was not in a `[]` binder.
However, the original plan for Lean4 was that one would only consider `[]` binders for typeclass resolution.
We suggest that we revert to the Lean3 protocol instead, and consider any local variable with class type as a candidate instance.

Finally, this instance could be made reasonable by allowing `{}` binders without names:
<<
instance reasonable (K E : Type) {Field K} [VectorSpace K E] [CompleteSpace K] : CompleteSpace E := {u := ()} -- should work in Lean4
>>
-/

axiom K : Type
instance K_Field : Field K := {u:=()}

#synth CompleteSpace K -- should fail quickly (and in particular, not run forever)

/-
The bad instance above could trigger a validation warning:

<<
instance bad (K E : Type) [Field K] [VectorSpace K E] [CompleteSpace K] : CompleteSpace E := {u := ()}
>>
-- Warning: argument #3 is a class that occurs in downstream arguments and not the return type.
-- You may want to replace [Field K] with {Field K} so typeclass resolution infers this instance after solving downstream instances.
-/

/-
The syntax `[Field K]` is ambiguous. It can be interpreted also as {Field K : _}. Note that we use this version all the time (e.g., {α β}).
-/
