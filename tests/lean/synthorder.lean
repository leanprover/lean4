class Foo (A : Type) (B : semiOutParam Type)

-- should be rejected, because C appears by itself in an out-param
instance [Foo A B] : Foo A (B × C) where

-- should be rejected, because non-out-param A can become an mvar
instance [Foo A Nat] : Foo Nat A where


set_option trace.Meta.synthOrder true

-- both instances should synthesize [Foo A B] first:
instance [Foo A B] [Foo B C] : Foo A C where
instance [Foo B C] [Foo A B] : Foo A C where

instance : Foo (Option A) A where



class One (α : Type)
class Two (α) [One α]
class TwoHalf (α) [One α] extends Two α
class Three (α : Type) (β : outParam Type) [One β] [Two β]
-- should both be accepted and synthesize `Three α β` first:
class Four (α : Type) (β : outParam Type) [One β] [TwoHalf β] extends Three α β
instance [One β] [TwoHalf β] [Three α β] : Four α β where

/-!
The structure elaborator needs to be able to define non-subobject projections with the same
signatures as subobject parents. This is a test to see that the synth order can still be computed.
-/
class C1 (α : Type) [Inhabited α]
-- Simulating a projection to another parent.
instance C1.toNonempty {α : Type} {inst : Inhabited α} [C1 α] : Nonempty α := ⟨default⟩
-- The parameters must come in a fixed order to be recognized as a projection.
instance C1.toNonempty' {α : Type} [DecidableEq α] {inst : Inhabited α} [C1 α] : Nonempty α := ⟨default⟩
