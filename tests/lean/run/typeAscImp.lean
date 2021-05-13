def Ctx := String → Type
abbrev State (Γ : Ctx) := {x : String} → Γ x

constant p {Γ : Ctx} (s : State Γ) : Prop

theorem ex {Γ : Ctx} (s : State Γ) (h : (a : State Γ) → @p Γ a) : @p Γ s :=
  h ‹_›
