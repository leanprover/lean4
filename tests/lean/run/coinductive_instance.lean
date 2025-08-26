import Init.Internal.Order
open Lean.Order

inductive InfSeq (r : α → α → Prop) : α → α → Prop where
  | step {b} : r a b → InfSeq r b c → InfSeq r a c
  | symm : InfSeq r a b → InfSeq r b a

inductive InfSeqFunctor (r : α → α → Prop) (infSeq : α → α → Prop)  : α → α → Prop where
  | step {b} : r a b → infSeq b c → InfSeqFunctor r infSeq a c
  | symm : infSeq a b → InfSeqFunctor r infSeq b a

  def InfSeqDef2 (r : α → α → Prop) : α → α → Prop := InfSeqFunctor r (InfSeqDef2 r)
    coinductive_fixpoint monotonicity fun p₁ p₂ p₁_le_p₂ x y as => by
      cases as
      case step z rel h2 =>
        apply InfSeqFunctor.step
        . exact rel
        . apply p₁_le_p₂
          exact h2
      case symm rel =>
        apply InfSeqFunctor.symm
        . apply p₁_le_p₂
          exact rel
