/-!
# `simp?` output order for roundtripping

This test checks that `simp?` roundtrips when expected to (as fixed in #9117).
-/

/-!
Collision of `not_imp` and `Classical.not_forall` (lemmas with different priority).
(discr tree keys: `Not (∀ _)`)
-/

/--
info: Try this: simp only [not_imp, Classical.not_forall]
---
error: unsolved goals
⊢ ∃ x, x ≤ 1 ∧ ¬x = 1
-/
#guard_msgs in
example : ¬∀ a : Nat, a ≤ 1 → a = 1 := by
  simp?

/--
error: unsolved goals
⊢ ∃ x, x ≤ 1 ∧ ¬x = 1
-/
#guard_msgs in
example : ¬∀ a : Nat, a ≤ 1 → a = 1 := by
  simp only [not_imp, Classical.not_forall]

/-!
Collision of multiple lemmas with the same priority: output in the order of being added to the simp
set: `exists_and_left`, `exists_eq_right_right`, `exists_prop`.
(discr tree keys: `Exists _ <other>`)
-/

/--
info: Try this: simp only [exists_and_left, exists_eq_right_right, exists_prop]
---
error: unsolved goals
x : Nat
⊢ 1 < x ∧ 0 < x
-/
#guard_msgs in
example (x : Nat) : ∃ (a : Nat) (_ : 0 < a) (_ : 1 < a), a = x := by
  simp?

/--
error: unsolved goals
x : Nat
⊢ 1 < x ∧ 0 < x
-/
#guard_msgs in
example (x : Nat) : ∃ (a : Nat) (_ : 0 < a) (_ : 1 < a), a = x := by
  simp only [exists_and_left, exists_eq_right_right, exists_prop]

/-!
`simp` **does not** guarantee roundtripping when custom simp sets are involved.

Explanation:
- Custom simp sets are always tried after normal simp lemmas
- Generalized lemmas are tried first
- `Bool.and_eq_decide` here is more general, so should be tried first;
  but it is in a custom simp set, so `eq_abc` takes priority
- Without custom simp sets, `Bool.and_eq_decide` will be tried first though
  and `eq_abc` will never get used
-/

def abc (x y : Bool) := x && !y

theorem eq_abc (x y : Bool) : (x && !y) = abc x y := by
  rfl

/--
info: Try this: simp only [eq_abc, Bool.and_eq_decide]
---
error: unsolved goals
x y : Bool
⊢ abc x y = decide (x = true ∧ y = true)
-/
#guard_msgs in
example (x y : Bool) : (x && !y) = (x && y) := by
  simp? only [bool_to_prop, eq_abc]

set_option linter.unusedSimpArgs false in
/--
error: unsolved goals
x y : Bool
⊢ decide (x = true ∧ (!y) = true) = decide (x = true ∧ y = true)
-/
#guard_msgs in
example (x y : Bool) : (x && !y) = (x && y) := by
  simp only [eq_abc, Bool.and_eq_decide]
