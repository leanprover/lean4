
-- This used to have
-- `case intro.intro.intro.intro.intro.intro.intro.inl`

/--
error: unsolved goals
case inl
a b c d e f g : Nat
h : False
⊢ False

case inr
a b c d e f g : Nat
h : False
⊢ False
-/
#guard_msgs in
example (h : ∃ a b c d e f g : Nat, False ∨ False) : False := by
  obtain ⟨a, b, c, d, e, f, g, h | h⟩ := h

/--
error: unsolved goals
case inl
a b c d e f g : Nat
h : False
⊢ False

case inr
a b c d e f g : Nat
h : False
⊢ False
-/
#guard_msgs in
example (h : ∃ a b c d e f g : Nat, False ∨ False) : False := by
  rcases h with ⟨a, b, c, d, e, f, g, h | h⟩

/--
error: unsolved goals
case left.inl
a b c d e f g : Nat
h : False
⊢ False

case left.inr
a b c d e f g : Nat
h : False
⊢ False
-/
#guard_msgs in
example (h : ∃ a b c d e f g : Nat, False ∨ False) : False ∧ False := by
  constructor
  · obtain ⟨a, b, c, d, e, f, g, h | h⟩ := h
  · sorry

-- We still get case names for `cases`

/--
error: unsolved goals
case intro
w✝ : Nat
h✝ : ∃ b c d e f g, False ∨ False
⊢ False
-/
#guard_msgs in
example (h : ∃ a b c d e f g : Nat, False ∨ False) : False := by
  cases h

/--
error: unsolved goals
case intro.intro.intro.intro.intro.intro.intro
a b c d e f g : Nat
h : False ∨ False
⊢ False
-/
#guard_msgs in
example (h : ∃ a b c d e f g : Nat, False ∨ False) : False := by
  cases h with | _ a h =>
  cases h with | _ b h =>
  cases h with | _ c h =>
  cases h with | _ d h =>
  cases h with | _ e h =>
  cases h with | intro f h =>
  cases h with | _ g h =>
  skip

-- And induction

/--
error: unsolved goals
case intro.intro.intro.intro.intro.intro.intro
a b c d e f g : Nat
h : False ∨ False
⊢ False
-/
#guard_msgs in
example (h : ∃ a b c d e f g : Nat, False ∨ False) : False := by
  induction h with | _ a h =>
  induction h with | _ b h =>
  induction h with | _ c h =>
  induction h with | _ d h =>
  induction h with | _ e h =>
  induction h with | intro f h =>
  induction h with | _ g h =>
  skip
