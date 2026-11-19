/-!
# Tests for `sym =>` interactive mode (PR1)

`intro` and `intros` internalize by default. Use `intro~` / `intros~` or
`(internalize := false)` to skip internalization.
-/

opaque myP : Nat → Prop
opaque myQ : Nat → Prop
opaque myR : Nat → Nat → Prop
opaque myF : Nat → Nat
axiom myP_myQ : myP x → myQ x
axiom myR_comm : myR x y → myR y x
axiom myR_trans : myR x y → myR y z → myR x z
axiom myP_step : myP x → myP (myF x)

/-! ## Test 1: sym => finish (no intro, finish handles everything) -/

example (x : Nat) : myP x → myQ x := by
  sym [myP_myQ] =>
    finish

/-! ## Test 2: sym => finish with multiple binders -/

example (x y z : Nat) : myR x y → myR y z → myR x z := by
  sym [myR_trans] =>
    finish

/-! ## Test 3: intro + finish (intro internalizes by default) -/

example (x : Nat) : myP x → myQ x := by
  sym [myP_myQ] =>
    intro h
    have h1 := h -- should work
    finish

/-! ## Test 4: intros + finish -/

example (x : Nat) : myP x → myQ x := by
  sym [myP_myQ] =>
    intros
    finish

/-! ## Test 5: apply backward rule -/

example (a b : Prop) (ha : a) (hb : b) : a ∧ b := by
  sym =>
    apply And.intro
    · tactic => exact ha
    · tactic => exact hb

/-! ## Test 6: apply with multiple subgoals -/

example (a b c : Prop) (ha : a) (hbc : b ∧ c) : a ∧ b ∧ c := by
  sym =>
    apply And.intro
    · tactic => exact ha
    · tactic => exact hbc

/-! ## Test 7: repeat instantiate for chain reasoning -/

example (x : Nat) : myP x → myP (myF (myF x)) := by
  sym [myP_step] =>
    intro h
    repeat instantiate only [→myP_step]
    finish

/-! ## Test 8: sym with only -/

example (x : Nat) : myP x → myQ x := by
  sym only [myP_myQ] =>
    finish

/-! ## Test 9: intro with named binders -/

example (x y : Nat) : myR x y → myR y x := by
  sym [myR_comm] =>
    intro h
    finish

/-! ## Test 10: intro~ skips internalization (explicit internalize needed) -/

example (x : Nat) : myP x → myQ x := by
  sym [myP_myQ] =>
    intro~ h
    internalize_all
    finish

/-! ## Test 11: intro (internalize := false) -/

example (x : Nat) : myP x → myQ x := by
  sym [myP_myQ] =>
    intro (internalize := false) h
    internalize 1
    finish

/-! ## Test 12: intros~ -/

example (x : Nat) : myP x → myQ x := by
  sym [myP_myQ] =>
    intros~
    internalize_all
    finish

/-! ## Test 13: tactic escape -/

example (x y : Nat) (h : x > y) : x > 0 := by
  sym =>
    tactic => omega

/-! ## Test 14: sym-only tactics rejected in grind => mode -/

/--
error: tactic is only available in `sym =>` mode
-/
#guard_msgs in
example (x : Nat) : myP x → myQ x := by
  grind [myP_myQ] =>
    intro h
    done

/-! ## Test 15: intro fails gracefully with no binders -/

/--
error: `intro` failed
-/
#guard_msgs in
example (x : Nat) (h : myP x) : myQ x := by
  sym [myP_myQ] =>
    intro _
    done

/-! ## Test 16: intros on fully applied goal -/

example (x : Nat) (h : myP x) : myQ x := by
  sym [myP_myQ] =>
    finish

/-! ## Test 17: by_contra + instantiate -/

example (x : Nat) : myP x → myQ x := by
  sym =>
    intro h
    by_contra
    instantiate only [→myP_myQ]

/-! ## Test 18: by_contra on already-False target fails -/

/--
error: `by_contra` failed, target is already `False`
-/
#guard_msgs in
example : False := by
  sym =>
    by_contra
    done

/-! ## Test 19: by_contra rejected in grind => mode -/

/--
error: tactic is only available in `sym =>` mode
-/
#guard_msgs in
example (x : Nat) : myP x → myQ x := by
  grind [myP_myQ] =>
    by_contra
    done

/-! ## Test 20: compact one-liner -/

example (x : Nat) : myP x → myQ x := by
  sym [myP_myQ] =>
    intro; by_contra; finish

example (p q : Prop) : p → q → p ∧ q := by
  sym =>
    intro hp hq
    apply And.intro
    apply hp
    apply hq

example (p q : Prop) : p → q → p ∧ q := by
  sym =>
    intro hp hq
    apply And.intro hp hq

example (p q : Prop) : p → q → p ∧ q := by
  sym =>
    intro hp hq
    tactic => exact And.intro hp hq

/-! ## lia/ring/linarith auto-introduce in sym mode -/

example (x y z : Nat) : x > 1 → x + y + z > 0 := by
  sym =>
    lia

example (x y z : Nat) : x > 1 → x + y + z > 0 := by
  sym =>
    intro
    lia

example (x : Nat) (h : x > 0) : x * x > 0 := by
  sym =>
    have := Nat.mul_pos h h

example (x y z : Nat) (h : x > 1) : x + y + z > 0 := by
  sym => lia

example (as : List Nat) (h : as = []) (h1 : as.length = b) : b = 0 := by
  sym =>
    instantiate
    by_contra
