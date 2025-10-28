set_option warn.sorry false
opaque f : Nat → Nat
opaque g : Nat → Nat
theorem fax : f (x + 1) = g (f x) := sorry

example : f (x + 100) = a := by
  grind =>
    set_config (gen := 15) -cutsat in
    -- The following instantiations should not fail since we set
    -- `gen` to 15
    use [fax]; use [fax]; use [fax]; use [fax]; use [fax]
    use [fax]; use [fax]; use [fax]; use [fax]; use [fax]
    use [fax]; use [fax]; use [fax]; use [fax]; use [fax]
    fail_if_success use [fax] -- should fail
    fail_if_success have : 2*x ≠ 1 -- cutsat is disabled
    set_config +cutsat in
    have : 2*x ≠ 1
    set_config (cutsat := false) in
    fail_if_success have : 3*x ≠ 1
    set_config (cutsat := true) in
    have : 3*x ≠ 1
    sorry
