def Set (α : Type) := α → Bool

def insertElem [DecidableEq α] (s : Set α) (a : α) : Set α :=
  fun x => a = x || s x

def contains (s : Set α) (a : α) : Bool :=
  s a

theorem contains_insert [DecidableEq α] (s : Set α) (a : α) : contains (insertElem s a) a := by
  simp [contains, insertElem]

grind_pattern contains_insert => contains (insertElem s a) a

-- TheoremPattern activation test

set_option trace.grind.ematch true
set_option trace.grind.ematch.pattern true

/-- info: [grind.ematch] activated `contains_insert`, [@contains #3 (@insertElem _ #2 #1 #0) #0] -/
#guard_msgs (info) in
example [DecidableEq α] (s₁ s₂ : Set α) (a₁ a₂ : α) :
        s₂ = insertElem s₁ a₁ → a₁ = a₂ → contains s₂ a₂ := by
  grind

/-- info: [grind.ematch] activated `contains_insert`, [@contains #3 (@insertElem _ #2 #1 #0) #0] -/
#guard_msgs (info) in
example [DecidableEq α] (s₁ s₂ : Set α) (a₁ a₂ : α) :
        ¬ contains s₂ a₂ → s₂ = insertElem s₁ a₁ → a₁ = a₂ → False := by
  grind

def a := 10
def b := 20
def foo (x : List Nat) (y : List Nat) := x ++ y ++ x

theorem fooThm : foo x [a, b] = x ++ [a, b] ++ x := rfl

/-- info: [grind.ematch.pattern] fooThm: [foo #0 `[[a, b]]] -/
#guard_msgs in
grind_pattern fooThm => foo x [a, b]


/--
info: [grind.internalize] foo x y
[grind.internalize] [a, b]
[grind.internalize] Nat
[grind.internalize] a
[grind.internalize] [b]
[grind.internalize] b
[grind.internalize] []
[grind.ematch] activated `fooThm`, [foo #0 `[[a, b]]]
[grind.internalize] x
[grind.internalize] y
[grind.internalize] z
-/
#guard_msgs (info) in
set_option trace.grind.internalize true in
example : foo x y = z → False := by
  fail_if_success grind
  sorry

theorem arrEx [Add α] (as : Array α) (h₁ : i < as.size) (h₂ : i = j) : as[i]+as[j] = as[i] + as[i] := by sorry


/--
info: [grind.ematch.pattern] arrEx: [@HAdd.hAdd #6 _ _ _ (@getElem _ `[Nat] _ _ _ #2 #5 _) (@getElem _ `[Nat] _ _ _ #2 #4 _)]
-/
#guard_msgs in
grind_pattern arrEx => as[i]+as[j]'(h₂▸h₁)
