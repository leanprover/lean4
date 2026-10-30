/-!
Regression test for #16034: `instantiate only [!thm]` uses the minimal indexable patterns of
`thm` even when `thm` is already registered with other patterns, so `grind?` keeps it in its
suggestions.
-/

def f (x : Nat) := x
def g (x : Nat) := x

theorem gf_eq (x : Nat) : g (f x) = g x := rfl
theorem g_iff (x : Nat) : g x = 0 ↔ x = 0 := by unfold g; rfl

attribute [grind =] gf_eq

/--
info: Try these:
  [apply] grind only [!gf_eq, g_iff]
  [apply] grind =>
    instantiate only [!gf_eq]
    instantiate only [g_iff]
-/
#guard_msgs in
example (x : Nat) : f x = 0 ↔ g x = 0 := by grind? [gf_eq, g_iff]

example (x : Nat) : f x = 0 ↔ g x = 0 := by
  grind only [!gf_eq, g_iff]

example (x : Nat) : f x = 0 ↔ g x = 0 := by
  grind =>
    instantiate only [!gf_eq]
    instantiate only [g_iff]

-- Without `!`, the registered theorem is used, and its pattern `g (f x)` does not match.
/--
error: `instantiate` tactic failed to instantiate new facts, use `show_patterns` to see active theorems and their patterns.
-/
#guard_msgs (error) in
example (x : Nat) : f x = 0 ↔ g x = 0 := by
  grind =>
    instantiate only [gf_eq]
