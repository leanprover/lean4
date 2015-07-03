-- HoTT
open eq


variables {A A' : Type} {a a' : A} {C : A → A' → Type} (p : a = a') (f : Π(b : A'), C a b) (b : A')

definition foo : (transport _ p f) b = p ▸ (f b) := sorry

definition bar : (p ▸ f) b = transport _ p (f b) := sorry

definition bla : (p ▸ f) b = p ▸ (f b) := sorry
