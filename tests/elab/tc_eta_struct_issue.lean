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
  map := Functor.map (f := F)

variable [LawfulApplicative F]

instance : LawfulApplicative (Op1 F) := by
  constructor
  repeat sorry
