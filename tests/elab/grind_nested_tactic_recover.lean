/-!
A failing `tactic =>` block in `sym =>` or `grind =>` mode must fail when error recovery is
disabled, instead of logging the error and admitting its goal. `Tactic.run` starts a `TacticM`
context with recovery enabled, and `Tactic.closeUsingOrAdmit` read recovery from that context
because the `withRecover` carrying the caller's setting was applied inside it. `first` disables
recovery for all alternatives but the last, so it shows the bug: it never fell through.
-/

example : True := by
  sym =>
    first
      (tactic => fail "first alternative")
      (tactic => trivial)

example : (1 : Nat) = 2 ∨ True := by
  sym =>
    first
      (tactic => exact Or.inl (by decide))
      (tactic => exact Or.inr trivial)

/--
error: second alternative
case grind
⊢ True
-/
#guard_msgs in
example : True := by
  sym =>
    first
      (tactic => fail "first alternative")
      (tactic => fail "second alternative")
