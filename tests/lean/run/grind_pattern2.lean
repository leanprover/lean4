module
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

/-- trace: [grind.ematch] activated `contains_insert`, [@contains #3 (@insertElem _ #2 #1 #0) #0] -/
#guard_msgs (trace) in
example [DecidableEq α] (s₁ s₂ : Set α) (a₁ a₂ : α) :
        s₂ = insertElem s₁ a₁ → a₁ = a₂ → contains s₂ a₂ := by
  grind

/-- trace: [grind.ematch] activated `contains_insert`, [@contains #3 (@insertElem _ #2 #1 #0) #0] -/
#guard_msgs (trace) in
example [DecidableEq α] (s₁ s₂ : Set α) (a₁ a₂ : α) :
        ¬ contains s₂ a₂ → s₂ = insertElem s₁ a₁ → a₁ = a₂ → False := by
  grind

def a := 10
def b := 20
def foo (x : List Nat) (y : List Nat) := x ++ y ++ x

theorem fooThm : foo x [a, b] = x ++ [a, b] ++ x := rfl

/-- trace: [grind.ematch.pattern] fooThm: [foo #0 `[[a, b]]] -/
#guard_msgs in
grind_pattern fooThm => foo x [a, b]


/--
trace: [grind.internalize] [0] x
[grind.internalize] [0] y
[grind.internalize] [0] z
[grind.internalize] [0] foo x y
-/
#guard_msgs (trace) in
set_option trace.grind.internalize true in
example : foo x y = z → False := by
  fail_if_success grind
  sorry

theorem arrEx [Add α] (as : Array α) (h₁ : i < as.size) (h₂ : i = j) : as[i]+as[j] = as[i] + as[i] := by sorry


/--
trace: [grind.ematch.pattern] arrEx: [@HAdd.hAdd #6 _ _ _ (@getElem (Array _) `[Nat] _ _ _ #2 #5 _) (@getElem (Array _) `[Nat] _ _ _ #2 #4 _)]
-/
#guard_msgs in
grind_pattern arrEx => as[i]+as[j]'(h₂▸h₁)

namespace Foo.Bla
set_option trace.grind.ematch false
set_option trace.grind.ematch.pattern false
opaque P : {n : Nat} → Fin (n+1) → Prop
/--
info: Try this:
  [apply] [grind .] for pattern: [@P #0 (@OfNat.ofNat (Fin _) `[0] _)]
-/
#guard_msgs in
@[grind] axiom Pax : @P n 0
end Foo.Bla
