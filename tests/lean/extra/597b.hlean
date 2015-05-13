open equiv
-- open equiv.ops
constants (A B : Type₀) (f : A ≃ B)
definition foo : A → B := f -- should fail
