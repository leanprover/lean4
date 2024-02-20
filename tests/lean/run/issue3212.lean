namespace SillyParam

set_option linter.unusedVariables false in
theorem nat_rec_with_string (some_param : String) {motive : Nat → Prop}
  (zero : motive .zero) (succ : ∀ n, motive n → motive (.succ n)) : ∀ n, motive n :=
  @Nat.rec motive zero succ

example (n m : Nat) (h : n ≠ zero) : Nat.add m n ≠ zero := by
  induction n using nat_rec_with_string
  case some_param =>
    show String
    exact "heh"
  case zero => sorry
  case succ => sorry

end SillyParam

namespace RestrictedMotive

axiom Restriction : (Nat → Prop) → Prop

axiom restricted_induction {motive : Nat → Prop} (h : Restriction motive)
  (zero : motive .zero) (succ : ∀ n, motive n → motive (.succ n)) : ∀ n, motive n

example (n m : Nat) (h : n ≠ zero) : Nat.add m n ≠ zero := by
  induction n using restricted_induction
  case h =>
    show Restriction _
    sorry
  case zero => sorry
  case succ => sorry

end RestrictedMotive


namespace DownInduction

axiom down_induction {motive : Nat → Prop} (u : Nat) (x : Nat)
  (le_u : x ≤ u) (start : motive u) (step : ∀ x, x < u → motive (x + 1) → motive x) : motive x

example (n m : Nat) (h : m * m < 100) (h2 : n ≤ m) : n * n < 100 := by
  induction n using down_induction
  case u => exact m -- (could have used `using down_induction (u := m)` of course)
  case le_u =>
    -- This does not work as hoped for yet: `induction` will revert `h2`, because it mentions `n`,
    -- but we’d like to keep it outside of the motive here.
    sorry
  case start => exact h
  case step x hlt IH =>
    have IH := IH hlt
    sorry

-- Unfortunately, this doesn’t work either:
--  example (n m : Nat) (h : m * m < 100) (h2 : n ≤ m) : n * n < 100 := by
--    induction n using down_induction (le_u := h2)
-- because after this, the target `n` is no longer a universally qualified variable
--
-- This probably could be made to work with a bit more refactoring.

end DownInduction
