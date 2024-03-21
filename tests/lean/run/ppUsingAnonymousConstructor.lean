/-!
# Tests for the `pp_using_anonymous_constructor` attribute
-/

/-!
Custom structure
-/

structure S where
  (x y : Nat)

/-- info: { x := 1, y := 2 } : S -/
#guard_msgs in #check {x := 1, y := 2 : S}

attribute [pp_using_anonymous_constructor] S
/-- info: ⟨1, 2⟩ : S -/
#guard_msgs in #check {x := 1, y := 2 : S}
