def Set (α : Type) := α → Bool

def insertElem [DecidableEq α] (s : Set α) (a : α) : Set α :=
  fun x => a = x || s x

def contains (s : Set α) (a : α) : Bool :=
  s a

theorem contains_insert [DecidableEq α] (s : Set α) (a : α) : contains (insertElem s a) a := by
  simp [contains, insertElem]

grind_pattern contains_insert => contains (insertElem s a) a

-- TheoremPattern activation test

set_option trace.grind.pattern true

/--
warning: declaration uses 'sorry'
---
info: [grind.pattern] activated `contains_insert`
-/
#guard_msgs in
example [DecidableEq α] (s₁ s₂ : Set α) (a₁ a₂ : α) :
        s₂ = insertElem s₁ a₁ → a₁ = a₂ → contains s₂ a₂ := by
  fail_if_success grind
  sorry

/--
warning: declaration uses 'sorry'
---
info: [grind.pattern] reinsert `contains_insert`
[grind.pattern] activated `contains_insert`
-/
#guard_msgs in
example [DecidableEq α] (s₁ s₂ : Set α) (a₁ a₂ : α) :
        ¬ contains s₂ a₂ → s₂ = insertElem s₁ a₁ → a₁ = a₂ → False := by
  fail_if_success grind
  sorry

def a := 10
def b := 20
def foo (x : List Nat) (y : List Nat) := x ++ y ++ x

theorem fooThm : foo x [a, b] = x ++ [a, b] ++ x := rfl

/--
info: [grind.pattern] fooThm: [foo #0 `[[a, b]]]
-/
#guard_msgs in
grind_pattern fooThm => foo x [a, b]


/--
warning: declaration uses 'sorry'
---
info: [grind.internalize] foo x y
[grind.pattern] activated `fooThm`
[grind.internalize] [a, b]
[grind.internalize] Nat
[grind.internalize] a
[grind.internalize] [b]
[grind.internalize] b
[grind.internalize] []
[grind.internalize] x
[grind.internalize] y
[grind.internalize] z
-/
#guard_msgs in
set_option trace.grind.internalize true in
example : foo x y = z → False := by
  fail_if_success grind
  sorry
