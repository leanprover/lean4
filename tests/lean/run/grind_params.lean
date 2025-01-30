def foo (x : Nat) := x + 2

example (f : Nat → Nat) : f (foo a) = b → f (c + 1) = d → c = a + 1 → b = d := by
  grind [foo]

opaque bla : Nat → Nat
theorem blathm : bla (bla x) = bla x := sorry

example : bla (foo a) = b → bla b = bla (a + 2) := by
  grind [foo, blathm]

example : bla (foo a) = b → bla b = bla (a + 2) := by
  grind [foo, = blathm]

/--
error: invalid `grind` forward theorem, theorem `blathm` does not have propositional hypotheses
-/
#guard_msgs (error) in
example : bla (foo a) = b → bla b = bla (a + 2) := by
  grind [foo, → blathm]

opaque P : Nat → Prop
opaque Q : Nat → Prop
opaque R : Nat → Prop

theorem pq : P x → Q x := sorry
theorem qr : Q x → R x := sorry

example : P x → R x := by
  grind [→ pq, → qr]

/--
error: `grind` failed
case grind
x : Nat
a✝ : P x
x✝ : ¬R x
⊢ False
[grind] Diagnostics
  [facts] Asserted facts
    [prop] P x
    [prop] ¬R x
  [eqc] True propositions
    [prop] P x
  [eqc] False propositions
    [prop] R x
  [ematch] E-matching patterns
    [thm] pq: [Q #1]
    [thm] qr: [Q #1]
-/
#guard_msgs (error) in
example : P x → R x := by
  grind [← pq, → qr]

example : P x → R x := by
  grind [← pq, ← qr]

attribute [grind] blathm

example : bla (bla (bla (bla x))) = bla x := by
  grind

example : bla (bla (bla (bla x))) = bla x := by
  fail_if_success grind [-blathm]
  sorry

example : bla (bla (bla (bla x))) = bla x := by
  grind only [blathm]

example : bla (bla (bla (bla x))) = bla x := by
  fail_if_success grind only
  sorry

/--
error: `pq` is not marked with the `[grind]` attribute
-/
#guard_msgs (error) in
example : P x → R x := by
  grind [-pq]
