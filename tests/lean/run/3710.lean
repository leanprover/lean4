def Set := Nat → Prop

namespace Set

def singleton (a : Nat) : Set := fun b ↦ b = a

def compl (s : Set) : Set := fun x ↦ ¬ s x

@[simp]
theorem compl_iff (s : Set) (x : Nat) : s.compl x ↔ ¬ s x := Iff.rfl

@[simp]
theorem singleton_iff {a b : Nat} : singleton b a ↔ a = b := Iff.rfl

open Classical

noncomputable def indicator (s : Set) (x : Nat) : Nat := if s x then 1 else 0

@[simp] -- remove `simp` attribute --> works (and the trace changes)
theorem indicator_of {s : Set} {a : Nat} (h : s a) : indicator s a = 1 := if_pos h

@[simp]
theorem indicator_of_not {s : Set} {a : Nat} (h : ¬ s a) : indicator s a = 0 := if_neg h

/--
info: Try this:
  simp only [compl_iff, singleton_iff, not_true_eq_false, not_false_eq_true, indicator_of_not]
-/
#guard_msgs in
theorem test : indicator (compl <| singleton 0) 0 = 0 := by
  simp? -- should not leave out `singleton_iff`

theorem test' : indicator (compl <| singleton 0) 0 = 0 := by
  simp only [compl_iff, singleton_iff, not_true_eq_false, not_false_eq_true, indicator_of_not]
