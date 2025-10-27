set_option warn.sorry false
opaque f : Nat → Nat
opaque g : Nat → Nat
theorem fax : f (x + 1) = g (f x) := sorry

example : f (x + 100) = a := by
  grind =>
    set_option gen 15 in
    -- The following instantiations should not fail since we set
    -- `gen` to 15
    use [fax]; use [fax]; use [fax]; use [fax]; use [fax]
    use [fax]; use [fax]; use [fax]; use [fax]; use [fax]
    use [fax]; use [fax]; use [fax]; use [fax]; use [fax]
    fail_if_success use [fax] -- should fail
    sorry
