module

public import UserAttr.BlaAttr

/-!
Regression test for issue #13725: `grind only [compact_set]` stopped using `closure_set1`
after the unrelated lemma `P_closure_set2` was tagged with the same custom `grind` attribute.
The partially activated `P_closure_set2` was reinserted into the first element of the
theorem array under the symbol `closure`, shadowing `closure_set1` stored in the
extension's element under the same key.
-/

def Set (α : Type _) : Type _ := α → Prop
def P {α} (_s : Set α) : Prop := True
def closure {α} (s : Set α) : Set α := s

def set1 {α} (_a : α) : Set α := fun _ ↦ False
def set2 {α} (_a : α) : Set α := fun _ ↦ False
def ℝ := Bool

@[compact_set =]
theorem closure_set1 (a : ℝ) : closure (set1 a) = set1 a := by
  simp [closure]

@[compact_set .]
theorem P_set1 {a : ℝ} : P (set1 a) := by trivial

#guard_msgs in
example (a : ℝ) : P (closure (set1 a)) := by grind only [compact_set]

@[compact_set .]
theorem P_closure_set2 {a : ℝ} : P (closure (set2 a)) := by trivial

#guard_msgs in
example (a : ℝ) : P (closure (set1 a)) := by grind only [compact_set]
