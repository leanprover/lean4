import Lean.Meta.Tactic.Simp.Simproc

/-!
# Behavior of `simp?`
-/

/-!
`simp?` lists the lemmas in order of being applied and not in the order of being declared.

Note: This is not always desirable, see #4615
-/

def x1 := 1
def x2 := 1
def x3 := 1
def x4 := 1

@[simp] theorem x2_eq_x3 : x2 = x3 := rfl
@[simp] theorem x3_eq_x4 : x3 = x4 := rfl
@[simp] theorem x1_eq_x2 : x1 = x2 := rfl

/--
info: Try this:
  simp only [x1_eq_x2, x2_eq_x3, x3_eq_x4]
-/
#guard_msgs in
example : x1 = x4 := by
  simp?

/-!
`simp?` lists every theorem being used only once.
-/

/--
info: Try this:
  simp only [x1_eq_x2, x2_eq_x3, x3_eq_x4]
-/
#guard_msgs in
example : x1 * x1 = x4 * x4 := by
  simp?

@[simp]
def test : Nat → Nat
  | 0 => 3
  | 1 => 5
  | 2 => 9
  | 3 => 4
  | 4 => 16
  | _ => 0

/-!
`simp?` mentions the name of the definition instead of the names of the equation lemmas.
-/

/--
info: Try this:
  simp only [test]
-/
#guard_msgs in
example : [test 3, test 2, test 4, test 5, test 0] = [4, 9, 16, 0, 3] := by
  simp?

/-!
`simp?` records names of `let` declarations being unfolded.
-/

/--
info: Try this:
  simp only [a]
-/
#guard_msgs in
example : let a := 5; a = 5 := by
  intro a
  simp? [a]

/-!
`simp?` shouldn't mention matcher equations.
-/

/--
info: Try this:
  simp only [h]
---
error: unsolved goals
a b : Nat
h : a = 3
⊢ 9 = b
-/
#guard_msgs in
example (h : a = 3) : (match (generalizing := false) a with | 0 => 7 | _ + 1 => 9) = b := by
  simp? [h]

/-!
`simp?` also mentions simprocs (builtin and non-builtin) but only if they succeeded.
-/

def y1 := 1
def y2 := 1

simproc rewriteY1 (y1) := fun _ => do
  return .done { expr := Lean.mkConst ``y2 }

simproc dontRewriteY2 (y2) := fun _ => do
  Lean.logInfo "was run"
  return .continue

/--
info: was run
---
info: Try this:
  simp only [rewriteY1]
-/
#guard_msgs in
example : y1 = y2 := by
  simp? -- rewriteY1 succeeds, dontRewriteY2 doesn't

/--
info: Try this:
  simp only [Nat.reduceAdd]
-/
#guard_msgs in
example : 1 + 1 = 2 := by
  simp?

/-!
The left arrow (`←`) should be grouped together with the lemma name.
-/

def z1 := 1
def z2 := 1
def z3 := 1

theorem very_long_lemma_oh_no_can_you_please_stop_we're_getting_to_the_limit : z1 = z2 := rfl
theorem wait_this_is_rewritten_backwards_and_wow_it's_very_clear_and_obvious : z3 = z2 := rfl

/--
info: Try this:
  simp only [very_long_lemma_oh_no_can_you_please_stop_we're_getting_to_the_limit,
      ← wait_this_is_rewritten_backwards_and_wow_it's_very_clear_and_obvious]
-/
#guard_msgs in
example : z1 = z3 := by
  simp? [very_long_lemma_oh_no_can_you_please_stop_we're_getting_to_the_limit,
    ← wait_this_is_rewritten_backwards_and_wow_it's_very_clear_and_obvious]
