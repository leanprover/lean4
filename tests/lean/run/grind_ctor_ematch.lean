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
    [prop] Even 12 → Even 14
    [prop] Even 10 → Even 12
    [prop] Even 8 → Even 10
    [prop] Even 6 → Even 8
  [eqc] True propositions
    [prop] Even 14 → Even 16
    [prop] Even 12 → Even 14
    [prop] Even 10 → Even 12
    [prop] Even 8 → Even 10
    [prop] Even 6 → Even 8
  [eqc] False propositions
    [prop] Even 16
  [ematch] E-matching patterns
    [thm] Even.plus_two: [Even (#1 + 2)]
    [thm] Even.zero: [Even `[0]]
  [limits] Thresholds reached
    [limit] maximum number of E-matching rounds has been reached, threshold: `(ematch := 5)`
    [limit] maximum term generation has been reached, threshold: `(gen := 5)`
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] Even.plus_two ↦ 5
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

/-- error: invalid E-matching theorem `Nat.succ`, type is not a proposition -/
#guard_msgs in
attribute [grind] Nat.succ
