def Ctx := String → Type
abbrev State (Γ : Ctx) := {x : String} → Γ x

opaque P {Γ : Ctx} (s : State Γ) : Prop

theorem ex {Γ : Ctx} (s : State Γ) (h : (a : State Γ) → @P Γ a) : @P Γ s :=
  h ‹_›
