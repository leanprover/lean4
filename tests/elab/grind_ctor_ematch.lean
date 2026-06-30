module
inductive Even : Nat → Prop
  | zero : Even 0
  | plus_two {n} : Even n → Even (n + 2)

example : Even 2 := by
  grind [Even.plus_two, Even.zero]

attribute [grind] Even.zero
attribute [grind] Even.plus_two

example : Even 2 := by
  grind

example : Even 4 := by
  grind

/--
error: `grind` failed
case grind
h : ¬Even 16
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] ¬Even 16
    [prop] Even 14 → Even 16
    [prop] Even 0
    [prop] Even 12 → Even 14
    [prop] Even 10 → Even 12
    [prop] Even 8 → Even 10
    [prop] Even 6 → Even 8
  [eqc] True propositions
    [prop] Even 0
    [prop] Even 14 → Even 16
    [prop] Even 12 → Even 14
    [prop] Even 10 → Even 12
    [prop] Even 8 → Even 10
    [prop] Even 6 → Even 8
  [eqc] False propositions
    [prop] Even 16
    [prop] Even 14
    [prop] Even 12
    [prop] Even 10
    [prop] Even 8
    [prop] Even 6
  [ematch] E-matching patterns
    [thm] Even.plus_two: [Even (#1 + 2)]
  [limits] Thresholds reached
    [limit] maximum number of E-matching rounds has been reached, threshold: `(ematch := 5)`
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] Even.plus_two ↦ 5
    [thm] Even.zero ↦ 1
-/
#guard_msgs (error) in
example : Even 16 := by
  grind

example : Even 16 := by
  grind (gen := 9) (ematch := 9)

opaque f : Nat → Nat

axiom fax (x : Nat) : f (f x) = f x

example : f (f (f x)) = f x := by
  grind [fax]

attribute [grind] fax

example : f (f (f x)) = f x := by
  grind

/-- error: invalid `grind` theorem, failed to find an usable pattern using different modifiers -/
#guard_msgs in
attribute [grind] Nat.succ
