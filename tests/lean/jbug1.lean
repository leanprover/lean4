import macros
import tactic

theorem le_iff (a b : Nat) : a ≤ b ↔ a < b ∨ a = b
:=
  iff_intro (
    assume H : a ≤ b,
    show a < b ∨ a = b, by skip
  )(
    assume H : a < b ∨ a = b,
    show a ≤ b, by skip
  )