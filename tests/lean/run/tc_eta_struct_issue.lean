-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.60constructor.60.20and.20.60Applicative.60/near/279949125

def Op1 (F : Type u → Type v) α := F α

namespace Op1

instance {F} [Functor F] : Functor (Op1 F) where
  map := @Functor.map F _

instance {F} [Functor F] [H : LawfulFunctor F] : LawfulFunctor (Op1 F) :=
sorry

variable {F} [Applicative F]

instance : Applicative (Op1 F) where
  pure := pure (f := F)
  seq f x := ((λ x f => f x) <$> x () <*> f : F _)

  -- The original version of this mwe did not specify the mapConst etc. instances,
  -- causing a non-defeq diamond.  Non-defeq diamonds for classes like Functor
  -- are not supported.

  -- map := Functor.map (f := F)

variable [LawfulApplicative F]
instance : LawfulApplicative (Op1 F) := by
  constructor
  repeat sorry
