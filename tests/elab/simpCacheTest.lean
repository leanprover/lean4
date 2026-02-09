/-!
Checks that the simp cache is consulted within `simpLoop`, not just in `simpMain`
-/


axiom testSorry : α
opaque a : Nat
opaque b : Nat
opaque c : Nat
opaque f : Nat → Nat
opaque P : Nat → Prop
theorem ab : a = b := testSorry
theorem bc : b = c := testSorry
theorem ba : b = a := testSorry
theorem fafb : f a = f b := testSorry

set_option trace.Meta.Tactic.simp.rewrite true


-- This trace should only mention one `bc` rewrite, not two.

/--
trace: [Meta.Tactic.simp.rewrite] bc:1000:
      b
    ==>
      c
[Meta.Tactic.simp.rewrite] h:1000:
      P c
    ==>
      True
[Meta.Tactic.simp.rewrite] ab:1000:
      a
    ==>
      b
[Meta.Tactic.simp.rewrite] h:1000:
      P c
    ==>
      True
[Meta.Tactic.simp.rewrite] and_self:1000:
      True ∧ True
    ==>
      True
-/
#guard_msgs in
example (h : P c) : P b ∧ P a := by simp [ab, bc, h]

-- Almost the same goal, but ordered differently.

/--
trace: [Meta.Tactic.simp.rewrite] ab:1000:
      a
    ==>
      b
[Meta.Tactic.simp.rewrite] bc:1000:
      b
    ==>
      c
[Meta.Tactic.simp.rewrite] h:1000:
      P c
    ==>
      True
[Meta.Tactic.simp.rewrite] h:1000:
      P c
    ==>
      True
[Meta.Tactic.simp.rewrite] and_self:1000:
      True ∧ True
    ==>
      True
-/
#guard_msgs in
example (h : P c) : P a ∧ P b := by simp [ab, bc, h]
