import Lean

section events
universe u v

-- | Polymorphic to and sum.
def pto (E: Type → Type u) (F: Type → Type v) :=
  ∀ T, E T → F T
def psum (E: Type → Type u) (F: Type → Type v) :=
  fun T => E T ⊕ F T
inductive PVoid: Type -> Type u
infixr:40 " ~> " => pto
infixr:60 " +' " => psum
end events



/- finite interaction trees -/
inductive Fitree (E : Type → Type u) (R : Type) where
  | Ret (r : R) : Fitree E R
  | Vis (e : E T) (k : T → Fitree E R) : Fitree E R

/-
Describe the ability to split a sum type L + R into LR.
-/
class SumSplit (L : Type -> Type) (LR : Type -> Type) (R : Type -> Type)  where
  redSplit: LR ~> L +' R

instance : SumSplit L L PVoid where
  redSplit := fun T l => Sum.inl l

instance : SumSplit L (L +' R) R where
  redSplit := fun T lr => lr

/- peel an itree along a split -/
def splitTree [SumSplit EL ELR ER] (t : Fitree ELR X) : Fitree (EL +' ER) X :=
  match t with
  | Fitree.Ret x => Fitree.Ret x
  | @Fitree.Vis _ _ T e k =>
     Fitree.Vis (SumSplit.redSplit _ e) fun t' =>
       let kt := k t'
       splitTree kt

def splitTree' [SumSplit EL ELR ER] (t : Fitree ELR X) : Fitree (EL +' ER) X :=
  match t with
  | .Ret x => Fitree.Ret x
  | .Vis e k =>
    .Vis (SumSplit.redSplit _ e) fun t' =>
      let kt := k t'
      splitTree' kt
