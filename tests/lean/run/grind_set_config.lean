set_option warn.sorry false
opaque f : Nat → Nat
opaque g : Nat → Nat
theorem fax : f (x + 1) = g (f x) := sorry

example : f (x + 100) = a := by
  grind -ring =>
    set_config (gen := 15) -lia in
    -- The following instantiations should not fail since we set
    -- `gen` to 15
    use [fax]; use [fax]; use [fax]; use [fax]; use [fax]
    use [fax]; use [fax]; use [fax]; use [fax]; use [fax]
    use [fax]; use [fax]; use [fax]; use [fax]; use [fax]
    fail_if_success use [fax] -- should fail
    fail_if_success have : 2*x ≠ 1 -- cutsat is disabled
    set_config +lia in
    have : 2*x ≠ 1
    set_config (lia := false) in
    fail_if_success have : 3*x ≠ 1
    set_config (lia := true) in
    have : 3*x ≠ 1
    sorry

opaque foo : Nat → Nat
axiom fooAx1 : foo (x + 1) = foo x
axiom fooAx2 : foo 0 ≥ 10

example : foo 40 ≥ 5 := by
  grind [fooAx1] =>
    have := fooAx2
    finish (gen := 50) (ematch := 50)

example : foo 10 ≥ 5 := by
  grind [fooAx1] =>
    have := fooAx2
    finish? (gen := 10) (ematch := 10)

attribute [grind] fooAx2

example : foo 30 ≥ 5 := by
  have := fooAx2
  grind => finish (gen := 50) (ematch := 50) [fooAx1]

example : foo 30 ≥ 5 := by
  have := fooAx2
  grind => finish? (gen := 50) (ematch := 50) [fooAx1]
