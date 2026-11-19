/-!
# Rewrite tactic "steals" goals
-/


/-!
https://github.com/leanprover/lean4/issues/10172

There were two metaprogramming bugs:
- `rw` didn't filter old vs new metavariables when coming up with new goals.
- it also didn't make the new metavariables be synthetic opaque, so the old one was
  being assigned, even with old vs new filtering.
-/
example (l m : List Nat) (i : Nat) (hi' : i < (l ++ m).length)
    (hh : ∀ hi, l[i]'hi = 5) : (l ++ m)[i] = 5 := by
  rw [List.getElem_append_left]
  · rw [hh] -- used to be Error: unsolved goal `i < l.length`
  · sorry -- used to be Error: No goals to be solved

/-!
While we're here, we could address a missing occurs check.

https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/rewrite.20with.20the.20goal/near/538108360
-/
/--
error: Occurs check failed: Expression
  ?k
contains the goal ?k
-/
#guard_msgs in
example : 1 = 2 := by
  refine ?k
  rw [?k]
