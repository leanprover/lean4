theorem Sum.inl_ne_inr' : inl a ≠ inr b := nofun

theorem Sum.inr_ne_inl' : inr b ≠ inl a := nofun

theorem Sum.inl_ne_inr'' : inl a ≠ inr b := by nofun

theorem Sum.inr_ne_inl'' : inr b ≠ inl a := by nofun

def f (a b : Bool) (_ : Sum.inr b ≠ Sum.inl a) : Nat := 0

example : f true true nofun = 0 := rfl
