section Order
open Lean.Order

instance [Pure m] : PartialOrder (OptionT m α) :=
  inferInstanceAs (PartialOrder (FlatOrder (pure none)))
noncomputable instance [Pure m] : CCPO (OptionT m α) :=
  inferInstanceAs (CCPO (FlatOrder (pure none)))
noncomputable instance [Monad m] [LawfulMonad m] : MonoBind (OptionT m) where
  bind_mono_left h := by
    cases h
    · show (OptionT.bind _ _ ⊑ OptionT.bind _ _)
      unfold OptionT.bind
      simp only [pure_bind]
      exact FlatOrder.rel.bot
    · exact FlatOrder.rel.refl
  bind_mono_right h := by
    show (OptionT.bind _ _ ⊑ OptionT.bind _ _)
    unfold OptionT.bind
    sorry
end Order
