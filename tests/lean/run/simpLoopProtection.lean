set_option linter.unusedSimpArgs false

axiom testSorry : α

opaque a : Nat
opaque b : Nat

theorem ab : a = b := testSorry
theorem ba : b = a := testSorry
theorem aa : a = id a := testSorry

/--
warning: Possibly looping simp theorem: `aa`

Note: Possibly caused by: `id`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
---
error: tactic 'simp' failed, nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : id a = 23 := by simp -failIfUnchanged only [aa, id]

-- also simp_all

/--
warning: Possibly looping simp theorem: `aa`

Note: Possibly caused by: `id`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
---
error: tactic 'simp' failed, nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : id a = 23 := by simp_all -failIfUnchanged only [aa, id]


-- Other exceptions do not trigger the loop check

/--
error: unsolved goals
⊢ b = 23
-/
#guard_msgs in
example : id b = 23 := by simp -failIfUnchanged only [aa, id]

/--
warning: Possibly looping simp theorem: `aa`

Note: Possibly caused by: `id`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
note: this linter can be disabled with `set_option linter.loopingSimpArgs false`
---
error: unsolved goals
⊢ b = 23
-/
#guard_msgs in
set_option linter.loopingSimpArgs true in
example : id b = 23 := by simp -failIfUnchanged only [aa, id]

/-- error: simp made no progress -/
#guard_msgs in
example : b = 23 := by simp only [aa, id]

/--
warning: Possibly looping simp theorem: `ab`

Note: Possibly caused by: `ba`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
---
warning: Possibly looping simp theorem: `ba`

Note: Possibly caused by: `ab`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
---
error: tactic 'simp' failed, nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : a = 23 := by simp -failIfUnchanged [ab, ba]

/--
warning: Possibly looping simp theorem: `ab`

Note: Possibly caused by: `ba`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
---
warning: Possibly looping simp theorem: `ba`

Note: Possibly caused by: `ab`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
---
error: tactic 'simp' failed, nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : a = 2*b := by simp -failIfUnchanged [ab, ba]

/--
warning: Possibly looping simp theorem: `← ab`

Note: Possibly caused by: `← ba`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
---
warning: Possibly looping simp theorem: `← ba`

Note: Possibly caused by: `← ab`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
---
error: tactic 'simp' failed, nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : a = 23 := by simp -failIfUnchanged [← ab, ← ba]

-- Local theorems are not checked for loops,
-- but are still applied when checking other rules

/--
warning: Possibly looping simp theorem: `ab`

Note: Possibly caused by: `h`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
---
error: tactic 'simp' failed, nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example (h : b = a) : a = 23 := by simp -failIfUnchanged [ab, h]

/-! Examples from the original RFC -/

variable (P : Nat → Prop)
/--
warning: Possibly looping simp theorem: `Nat.add_assoc`

Note: Possibly caused by: `(Nat.add_assoc _ _ _).symm`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
---
warning: Possibly looping simp theorem: `(Nat.add_assoc _ _ _).symm`

Note: Possibly caused by: `Nat.add_assoc`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
---
error: tactic 'simp' failed, nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example (a b c : Nat) : P (a + b + c) := by simp [Nat.add_assoc, (Nat.add_assoc _ _ _).symm]

inductive Tree (α : Type) where | node : α → List (Tree α) → Tree α
def Tree.children : Tree α → List (Tree α) | .node _ ts => ts
def Tree.size (t : Tree α) := 1 + List.sum (t.children.attach.map (fun ⟨c,_⟩  => c.size))
decreasing_by simp_wf; cases t; simp_all [Tree.children]; decreasing_trivial

/--
warning: Possibly looping simp theorem: `Tree.size.eq_1`

Note: Possibly caused by: `Tree.size`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
---
error: tactic 'simp' failed, nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example (t : Tree α) : 0 < t.size := by simp [Tree.size]


/--
Identifiyng looping theorems by their origin is not enough,
as the elements of conjunctions would clash, as shown by these:

(The error message isn't great yet, but it's a corner case)
-/

theorem b1ab : b = 1 ∧ a = b := testSorry
theorem baab : b = a ∧ a = b := testSorry

/--
error: unsolved goals
P : Nat → Prop
⊢ 1 > 0
-/
#guard_msgs in
example : a > 0 := by simp only [b1ab]

/--
warning: Possibly looping simp theorem: `baab`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
---
warning: Possibly looping simp theorem: `baab`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
---
error: tactic 'simp' failed, nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : a > 0 := by simp only [baab]

-- Same, with local theorems (should we ever support them):

/--
error: unsolved goals
P : Nat → Prop
a b : Nat
h1 : b = 1 ∧ a = b
h2 : 1 > 0
⊢ True
-/
#guard_msgs in
example
  (a b : Nat)
  (h1 : b = 1 ∧ a = b )
  (h2 : a > 0) : True := by
  simp only [h1] at h2


/-!
Unfolding should not confuse it.
(Error message is not optimal as it does not mention the unfolded definition.)
-/

def c := a
def ac : a = c := rfl
def ca : c = a := rfl
def d := c
def dc : d = c := rfl

/--
warning: Possibly looping simp theorem: `c.eq_1`

Note: Possibly caused by: `ac` and `c`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
---
warning: Possibly looping simp theorem: `ac`

Note: Possibly caused by: `c`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
---
error: tactic 'simp' failed, nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : c > 0 := by simp only [c, ac]

/--
warning: Possibly looping simp theorem: `dc`

Note: Possibly caused by: `c` and `ac`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
---
warning: Possibly looping simp theorem: `c.eq_1`

Note: Possibly caused by: `ac` and `c`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
---
warning: Possibly looping simp theorem: `ac`

Note: Possibly caused by: `c`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
---
error: tactic 'simp' failed, nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : d > 0 := by simp only [dc, c, ac]


/--
warning: Possibly looping simp theorem: `c.eq_1`

Note: Possibly caused by: `ac` and `c`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
---
warning: Possibly looping simp theorem: `ac`

Note: Possibly caused by: `c`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
---
error: tactic 'simp' failed, nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : a > 0 := by simp only [c, ac]

example (h : c = 1) : d > 0 := by simp only [dc, h, ca, ac, Nat.one_pos]


/-!
Simp? does not print the warnings for now. Let’s see if users find that helpful or confusing.
-/

/--
error: tactic 'simp' failed, nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : d > 0 := by simp? only [dc, ca, ac]; exact testSorry

/-!
But we can turn it on:
-/
set_option linter.loopingSimpArgs true in
/--
error: tactic 'simp' failed, nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : d > 0 := by simp? only [dc, ca, ac]; exact testSorry

/-- info: Try this: simp only [dc, h, Nat.one_pos] -/
#guard_msgs in
example (h : c = 1) : d > 0 := by simp? only [dc, h, ca, ac, Nat.one_pos]


/-! An example where a second rewrite rules makes the looping rule looping,
without being itself looping.
-/

opaque f : Nat → Nat
theorem fbfa : f b = f a := testSorry
theorem fbffa : f b = f (f a) := testSorry

-- This one doesn't actually trigger because `simpLoop` does not recurse when
-- the expression is the same after `post`. Also see issue #8864

/--
error: unsolved goals
P : Nat → Prop
⊢ 0 < f a
-/
#guard_msgs in
example : 0 < f a := by simp -failIfUnchanged [fbfa, ab]

/--
warning: Possibly looping simp theorem: `fbffa`

Note: Possibly caused by: `ab`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
---
error: tactic 'simp' failed, nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : 0 < f a := by simp -failIfUnchanged [fbffa, ab]
