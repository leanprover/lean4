module
reset_grind_attrs%
def Set (α : Type) := α → Bool

def insertElem [DecidableEq α] (s : Set α) (a : α) : Set α :=
  fun x => a = x || s x

def contains (s : Set α) (a : α) : Bool :=
  s a

namespace Set

theorem contains_insert [DecidableEq α] (s : Set α) (a : α) : contains (insertElem s a) a := by
  simp [contains, insertElem]

scoped grind_pattern contains_insert => contains (insertElem s a) a

end Set

example [DecidableEq α] (s₁ s₂ : Set α) (a₁ a₂ : α) :
        s₂ = insertElem s₁ a₁ → a₁ = a₂ → contains s₂ a₂ := by
  fail_if_success grind -- should fail
  open Set in grind -- scoped pattern was activated, it should work now

example [DecidableEq α] (s₁ s₂ : Set α) (a₁ a₂ : α) :
        s₂ = insertElem s₁ a₁ → a₁ = a₂ → contains s₂ a₂ := by
  fail_if_success grind -- should fail
  intros; subst s₂ a₁; apply Set.contains_insert

open Set in
example [DecidableEq α] (s₁ s₂ : Set α) (a₁ a₂ : α) :
        s₂ = insertElem s₁ a₁ → a₁ = a₂ → contains s₂ a₂ := by
  grind -- should work

example [DecidableEq α] (s₁ s₂ : Set α) (a₁ a₂ : α) :
        s₂ = insertElem s₁ a₁ → a₁ = a₂ → contains s₂ a₂ := by
  fail_if_success grind -- should fail
  intros; subst s₂ a₁; apply Set.contains_insert


-- TheoremPattern activation test

def a := 10
def b := 20
def foo (x : List Nat) (y : List Nat) := x ++ y ++ x

theorem fooThm : foo x [a, b] = x ++ [a, b] ++ x := rfl

section
local grind_pattern fooThm => foo x [a, b]

/-- trace: [grind.ematch.instance] fooThm: foo x [a, b] = x ++ [a, b] ++ x -/
#guard_msgs in
set_option trace.grind.ematch.instance true in
example : xs = [a, b] → foo x xs = x ++ [a, b] ++ x := by
  grind

end

example : xs = [a, b] → foo x xs = x ++ [a, b] ++ x := by
  fail_if_success grind -- should fail, `local grind_pattern` is not active anymore
  intro; subst xs; apply fooThm
