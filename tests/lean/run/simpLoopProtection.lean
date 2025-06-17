axiom testSorry : α

opaque a : Nat
opaque b : Nat

theorem ab : a = b := testSorry
theorem ba : b = a := testSorry
theorem aa : a = id a := testSorry

/--
warning: Ignoring looping simp theorem: aa

Note: These theorems may also play a role:
      id

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.

Hint: You can disable this check using `simp -loopProtection`.
---
error: unsolved goals
⊢ a = 23
-/
#guard_msgs in
example : id a = 23 := by
  simp -failIfUnchanged only [aa, id]

/--
warning: Ignoring jointly looping simp theorems: ab and ba

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.

Hint: You can disable this check using `simp -loopProtection`.
---
error: unsolved goals
⊢ a = 23
-/
#guard_msgs in
example : a = 23 := by
  simp +loopProtection -failIfUnchanged [ab, ba]

/--
warning: Ignoring jointly looping simp theorems: ab and ba

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.

Hint: You can disable this check using `simp -loopProtection`.
---
warning: Ignoring jointly looping simp theorems: ba and ab

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.

Hint: You can disable this check using `simp -loopProtection`.
---
error: unsolved goals
⊢ a = 2 * b
-/
#guard_msgs in
example : a = 2*b := by simp +loopProtection -failIfUnchanged [ab, ba]

/--
warning: Ignoring jointly looping simp theorems: ← ba and ← ab

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.

Hint: You can disable this check using `simp -loopProtection`.
---
error: unsolved goals
⊢ a = 23
-/
#guard_msgs in
example : a = 23 := by simp +loopProtection -failIfUnchanged [← ab, ← ba]

-- Local theorems are not considered during loop checking:

/--
error: tactic 'simp' failed, nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example (h : b = a) : a = 23 := by simp +loopProtection -failIfUnchanged [ab, h]

-- ..but still are applied
example (h : b = 23) : a = 23 := by simp +loopProtection -failIfUnchanged [ab, h]

/-! Check that we cache the protection result (both positive and negative) -/

opaque id' : Nat → Nat
theorem id'_eq (n : Nat) : id' n = n := testSorry
theorem id'_eq_bad (n : Nat) : id' n = id' (id' n) := testSorry

/--
trace: [Meta.Tactic.simp.loopProtection] loop-checking id'_eq:1000
[Meta.Tactic.simp.loopProtection] loop-checking eq_self:1000
-/
#guard_msgs in
set_option trace.Meta.Tactic.simp.loopProtection true in
example : id' 1 + id' 2 = id' 3 := by simp +loopProtection -failIfUnchanged [id'_eq]

/--
warning: Ignoring looping simp theorem: id'_eq_bad

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.

Hint: You can disable this check using `simp -loopProtection`.
---
error: unsolved goals
⊢ id' 1 + id' 2 = id' 3
---
trace: [Meta.Tactic.simp.loopProtection] loop-checking id'_eq_bad:1000
  [Meta.Tactic.simp.loopProtection] loop-checking id'_eq_bad:1000
    [Meta.Tactic.simp.loopProtection] loop detected: id'_eq_bad
-/
#guard_msgs in
set_option trace.Meta.Tactic.simp.loopProtection true in
example : id' 1 + id' 2 = id' 3 := by simp +loopProtection -failIfUnchanged [id'_eq_bad]


/-! Examples from the original RFC -/

variable (P : Nat → Prop)
/--
warning: Ignoring jointly looping simp theorems: Nat.add_assoc and (Nat.add_assoc _ _ _).symm

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.

Hint: You can disable this check using `simp -loopProtection`.
---
error: simp made no progress
-/
#guard_msgs in
example (a b c : Nat) : P (a + b + c) := by simp +loopProtection [Nat.add_assoc, (Nat.add_assoc _ _ _).symm]

inductive Tree (α : Type) where | node : α → List (Tree α) → Tree α
def Tree.children : Tree α → List (Tree α) | .node _ ts => ts
def Tree.size (t : Tree α) := 1 + List.sum (t.children.attach.map (fun ⟨c,_⟩  => c.size))
decreasing_by simp_wf; cases t; simp_all [Tree.children]; decreasing_trivial

/--
warning: Ignoring looping simp theorem: Tree.size.eq_1

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.

Hint: You can disable this check using `simp -loopProtection`.
---
error: simp made no progress
-/
#guard_msgs in
example (t : Tree α) : 0 < t.size := by simp +loopProtection [Tree.size]


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
example : a > 0 := by simp +loopProtection only [b1ab]

/--
warning: Ignoring jointly looping simp theorems: baab and baab

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.

Hint: You can disable this check using `simp -loopProtection`.
---
error: simp made no progress
-/
#guard_msgs in
example : a > 0 := by simp +loopProtection only [baab]

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
  simp +loopProtection only [h1] at h2


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
warning: Ignoring looping simp theorem: ac

Note: These theorems may also play a role:
      c

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.

Hint: You can disable this check using `simp -loopProtection`.
---
error: unsolved goals
P : Nat → Prop
⊢ a > 0
-/
#guard_msgs in
example : c > 0 := by simp only [c, ac]

/--
warning: Ignoring looping simp theorem: ac

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.

Hint: You can disable this check using `simp -loopProtection`.
---
error: unsolved goals
P : Nat → Prop
⊢ a > 0
-/
#guard_msgs in
example : d > 0 := by simp only [dc, c, ac]


/--
warning: Ignoring looping simp theorem: ac

Note: These theorems may also play a role:
      c

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.

Hint: You can disable this check using `simp -loopProtection`.
---
error: simp made no progress
-/
#guard_msgs in
example : a > 0 := by simp only [c, ac]

/-!
Check that we do not get warnings for theorems not actually encountered, because
of a local theorem that prevents them from rewriting in the first place.
-/
example (h : c = 1) : d > 0 := by simp only [dc, h, ca, ac, Nat.one_pos]


/-!
Check that `simp?` does not leak the rewrites done during loop protection.
-/
/--
warning: Ignoring jointly looping simp theorems: ca and ac

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.

Hint: You can disable this check using `simp -loopProtection`.
---
info: Try this: simp only [dc]
-/
#guard_msgs in
example : d > 0 := by simp? only [dc, ca, ac]; exact testSorry

/-- info: Try this: simp only [dc, h, Nat.one_pos] -/
#guard_msgs in
example (h : c = 1) : d > 0 := by simp? only [dc, h, ca, ac, Nat.one_pos]


/-! An example where a second rewrite rules makes the looping rule looping,
without being itself looping. Needs diagnostics to see it!
-/

opaque f : Nat → Nat
theorem fbfa : f b = f a := testSorry

/--
warning: Ignoring looping simp theorem: fbfa

Note: These theorems may also play a role:
      ab

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.

Hint: You can disable this check using `simp -loopProtection`.
---
error: unsolved goals
P : Nat → Prop
⊢ 0 < f b
-/
#guard_msgs in
example : f b > 0 := by
  simp +loopProtection -failIfUnchanged [fbfa, ab]
